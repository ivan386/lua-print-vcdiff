-- lua 5.3

local show_data --= true
local utf8_data = true
local extended_info --= true

function to_stream(data)
	local pos = 1
	return {
		read = function(this, count)
			local part = data:sub(pos, pos + count - 1)
			pos = pos + count
			return part
		end,
		seek = function(this)
			return pos - 1
		end
	}
end

function to_hex(data)
	if type(data) == "string" then
		return ('%02X%02X%02X%02X'):format(data:byte(1,-1))
	end
end

function to_bits(int)
	local bits = ""
	repeat
		bits = (int & 1)..bits
		int = int >> 1
	until (int == 0)
	return "0B"..bits
end

function read_byte(stream)
	local c = stream:read(1)
	if c then
		return c:byte()
	end
end

function prefix(chr, size, value)
	if #tostring(value) < size then
		return (chr:rep(size)..value):sub(-size)
	end
	return value
end

function sufix(chr, size, value)
	if #tostring(value) < size then
		return (value..chr:rep(size)):sub(1,size)
	end
	return value
end

function serialize_string(value, js, valid_utf8)
    if type(value) == "string" then
        local patern = "(['\\%c])([0-9]?)"
        local qa = "'"
        if js or value:find("'", 1, true) then
            patern = '(["\\%c])([0-9]?)'
            qa = '"'
        end
        
        local codes = {
            ['"'] = '\\"',
            ["'"] = "\\'",
            ['\\'] = '\\\\',
            ['\b'] = '\\b',
            ['\f'] = '\\f',
            ['\n'] = '\\n',
            ['\r'] = '\\r',
            ['\t'] = '\\t',
            ['\v'] = '\\v'
        }
		
		local replace_char = function(chr, digit)
			digit = digit or ""
			
            local code = codes[chr]
            
            if code then
                return code..digit
            end

            if chr == '\a' and not js then
                return '\\a'..digit
            elseif chr == '\0' and #digit == 0 then
                return '\\0'
            end
            
            local b = string.byte(chr)
            if js then
                return string.format('\\x%02X%s', b, digit)
            else
                if #digit == 1 then
                    if string.len(b) == 1 then return "\\00"..b..digit end
                    if string.len(b) == 2 then return "\\0"..b..digit end
                end
            end
            return "\\"..b..digit
        end
        
		local to_valid_utf8 = function(str)
			local i = 1
			local l, p = utf8.len(str, i)
			
			if l then
				return str
			end
			
			if js then
				str = str:gsub("([\xC2-\xC3])([\x80-\xBF])([0-9]?)", function(first, second, digit)
					return replace_char(first)..replace_char(second, digit)
				end)
			end
			
			local valid_utf8 = ""
			while not l do
				local digit = str:match("[0-9]?", p+1)
				if p > i then
					valid_utf8 = valid_utf8 .. str:sub(i, p-1) .. replace_char(str:sub(p, p), digit)
				else
					valid_utf8 = valid_utf8 .. replace_char(str:sub(p, p), digit)
				end
				if #digit == 1 then
					i = p + 2
				else
					i = p + 1
				end
				l, p = utf8.len(str, i)
			end
			if l > 0 then
				valid_utf8 = valid_utf8 .. str:sub(i)
			end
			
			return valid_utf8
		end
		
		local v = string.gsub(value, patern, replace_char)
		
		if valid_utf8 then
			v = to_valid_utf8(v)
		end
		
        return qa..v..qa
    else
        return nil, ("value %s in not string"):format(type(value))
    end
end

--------------------------------------------------------------------------------------

function read_int(stream)
	local int = 0
	local size = 0
	repeat
		local b = stream:read(1):byte()
		int = (int << 7) | ( b & 127 )
		size = size + 1
	until b < 128
	return int
end

function read_header(stream)
	local header = {}
	header.magik = stream:read(3)
	header.version = read_byte(stream)
	header.indicator = read_byte(stream)
	if header.indicator & 1 == 1 then
		header.compress_id = read_byte(stream)
	end
	if header.indicator & 2 == 2 then
		assert(false, "code table not supported")
		header.code_table = stream:read(read_int(stream))
	end
	if header.indicator & (1<<2) == (1<<2) then -- xdelta3 extension (application header)
		header.app_header = stream:read(read_int(stream))
	end
	return header
end

function read_window_header(stream)
	local window = {}
	window.indicator = read_byte(stream)
	if not window.indicator then
		return
	end
	if window.indicator & 3 > 0 then
		window.segment_length = read_int(stream)
		window.segment_position = read_int(stream)
	end
	window.delta_length = read_int(stream)
	window.target_length = read_int(stream)
	window.delta = {
		indicator = read_byte(stream),
		data_length = read_int(stream),
		instructions_length = read_int(stream),
		addresses_length = read_int(stream)
	}
	if window.indicator & (1 << 2) == (1 << 2) then -- xdelta3 extension (checksum)
		window.adler32 = stream:read(4)
	end
	return window
end

function cache_init(window_header, window_offset)
	return {
		segment_length = window_header.segment_length or nil,
		here = window_header.segment_length or 0,
		near_size = 4, -- mode: 2, 3, 4, 5
		same_size = 3, -- mode: 6, 7, 8
		next_near_index = 0,
		near = {},
		same = {}
	}
end

function cache_update(address_cache, address)
	assert(address, "address empty")
	
	if address_cache.near_size > 0 then
		address_cache.near[address_cache.next_near_index] = address
		address_cache.next_near_index = (address_cache.next_near_index + 1) % address_cache.near_size
	end
	
	if address_cache.same_size > 0 then
		local same_index = address % (address_cache.same_size * 256)
		address_cache.same[same_index] = address
	end
	
	return address
end

function update_here(address_cache, size)
	address_cache.here = address_cache.here + size
	return size
end

function decode_address(address_stream, copy_mode, address_cache)
	local address
	local mode_name
	local same_index
	local address_value
	local cache_value
	if copy_mode == 0 then
		mode_name = "self"
		address_value = read_int( address_stream )
		address = address_value
	elseif copy_mode == 1 then
		mode_name = "here"
		address_value = read_int( address_stream )
		address = address_cache.here - address_value
	elseif copy_mode < 2 + address_cache.near_size then
		mode_name = "near"
		local near_index = copy_mode - 2
		address_value = read_int( address_stream )
		cache_value = address_cache.near[near_index] or 0
		assert(cache_value, "near slot empty")
		address = cache_value + address_value
	elseif copy_mode < 2 + address_cache.near_size + address_cache.same_size then
		mode_name = "same"
		local same_mode = copy_mode - (2 + address_cache.near_size)
		address_value = read_byte( address_stream )
		same_index = same_mode * 256 + address_value
		address = address_cache.same[same_index] or 0
		assert(address,  "same slot empty")
	end
	
	return cache_update(address_cache,  address), mode_name, address_value, cache_value
end

function decode_standart_instructions(instructions_stream, address_stream, address_cache)
	local index = read_byte(instructions_stream)
	
	local decode = function(copy_mode, copy_size)
		local address, mode_name, address_value, cache_value  =
			decode_address(address_stream, copy_mode, address_cache)
			
		update_here( address_cache, copy_size )
		
		local use_source = true
		local source_address = address
		
		if not address_cache.segment_length then
			use_source = false
		elseif address >= address_cache.segment_length then
			use_source = false
			source_address = address - address_cache.segment_length
		end
		
		return use_source, source_address, mode_name, copy_mode, address_value, address, cache_value
	end

	if index == 0 then
		return {"RUN", update_here(address_cache, read_int(instructions_stream))}, nil, index
	end
	
	if index == 1 then
		return {"ADD", update_here(address_cache, read_int(instructions_stream))}, nil, index
	end
	
	local copy_modes = {
		[19]  = 0, [35] = 1, [51]  = 2, [67]  = 3, 
		[83]  = 4, [99] = 5, [115] = 6, [131] = 7,
		[147] = 8 }
	
	if copy_modes[index] then
		local copy_size = read_int(instructions_stream)
		return { "CPY", copy_size , decode(copy_modes[index] , copy_size) }, nil, index
	end
	
	if index < 19 then
		return { "ADD", update_here(address_cache, index - 1) }, nil, index
	end
	
	if index < 163 then
		local copy_size = 3 + (index - 19) % 16
		return { "CPY", copy_size , decode( (index - 19) // 16,  copy_size ) }, nil, index
	end
	
	if index < 235 then
		local copy_mode = (index - 163) // 12
		local sizes = (index - 163) % 12
		local copy_size = 4 + sizes % 3
		local add_size = update_here(address_cache, 1 + sizes // 3)
		return { "ADD", add_size }, { "CPY", copy_size, decode( copy_mode, copy_size ) }, index
	end
	
	if index < 247 then
		local copy_mode = 6 + (index - 235) // 4
		local add_size = update_here(address_cache, 1 + ((index - 235) % 4))
		return { "ADD", add_size }, { "CPY", 4, decode( copy_mode, 4 ) }, index
	end
	
	if index < 256 then
		return { "CPY", 4, decode( index - 247, 4 ) }, {"ADD", update_here(address_cache, 1)}, index
	end
end

function print_header(header, header_size)
	io.write(([[

VCDIFF version:               %s
VCDIFF header size:           %s
VCDIFF header indicator:      %s
]]):format(header.version, header_size, to_bits(header.indicator)))
	
	if header.compress_id then
		io.write(([[
VCDIFF secondary compressor:  %s
]]):format(header.compress_id))
	end
	
	if header.app_header then
		io.write(([[
VCDIFF application header:    %s
]]):format(serialize_string(header.app_header, true, utf8_data)))
	end
end

function print_window_header(window_header, window_index, window_offset)
		io.write(([[


VCDIFF window number:         %s
VCDIFF window indicator:      %s
]]):format(window_index, to_bits(window_header.indicator)))
		
		if window_header.adler32 then
			io.write(([[
VCDIFF adler32 checksum:      %s
]]):format(to_hex(window_header.adler32)))
		end
		
		io.write(([[
VCDIFF window at offset:      %s
]]):format(window_offset))
	
		if window_header.segment_length and window_header.segment_position then
			io.write(([[
VCDIFF copy window length:    %s
VCDIFF copy window offset:    %s
]]):format(window_header.segment_length, window_header.segment_position))
		end
	
		io.write(([[
VCDIFF delta encoding length: %s
VCDIFF target window length:  %s
VCDIFF delta indicator:       %s
VCDIFF data section length:   %s
VCDIFF inst section length:   %s
VCDIFF addr section length:   %s

]]):format(window_header.delta_length, window_header.target_length, to_bits(window_header.delta.indicator), window_header.delta.data_length, window_header.delta.instructions_length, window_header.delta.addresses_length ))

	if (show_data or extended_info) then
		io.write([[
  Offset Code Type1 Size1  @Addr1 
         +    Type2 Size2  @Addr2
		]])
	else
		io.write([[
  Offset Code Type1 Size1  @Addr1 + Type2 Size2 @Addr2
		]])
	end
end

function main(file_name)
	local input = io.open(file_name,"rb")
	--io.output("vcdiff.txt")
	
	local header = read_header(input)
	
	print_header(header, input:seek())

	local window_index = 0
	local window_offset = 0
	local window_header = read_window_header(input)
	while window_header do
		print_window_header(window_header, window_index, window_offset)
		
		assert(window_header.delta.indicator == 0, "compression not supported")
		
		
		local data_stream = to_stream(input:read(window_header.delta.data_length))
		local instructions_stream = to_stream(input:read(window_header.delta.instructions_length))
		local addresses_stream = to_stream(input:read(window_header.delta.addresses_length))
		
		local address_cache = cache_init(window_header, window_offset)
		
		local start_pos = instructions_stream:seek() 
		while instructions_stream:seek() - start_pos < window_header.delta.instructions_length do
			
			io.write("\n  ", prefix("0", 6, window_offset + address_cache.here - (window_header.segment_length or 0)) , " ")
			
			local first_inst, second_inst, index = decode_standart_instructions(instructions_stream, addresses_stream, address_cache)
			
			io.write(prefix("0", 3, index), "  ")
			
			for index, instruction in ipairs({first_inst, second_inst}) do
				local name, size, use_source, address, mode_name, mode, address_value, result_address, cache_value = table.unpack(instruction)
				if (show_data or extended_info) and index > 1 then
					io.write("\n         +    ")
				end
				
				if name == "CPY" then
					if use_source then
						address_prefix = "S@"
						address = window_header.segment_position + address
					else
						address_prefix = "T@"
					end
				
					io.write(name, "_", mode, " ", prefix(" ", 6, size), " ", address_prefix, sufix(" ", 5, address))
					if extended_info then
						io.write("\t", mode_name)
						
						if result_address then
							io.write("\tRA: ", sufix(" ", 5, result_address))
						end
						if address_value then
							io.write("\tAV: ", sufix(" ", 5, address_value))
						end
						if cache_value then
							io.write("\tCV: ", sufix(" ", 5, cache_value))
						end
					end
				else
					io.write(name, " ", prefix(" ", 8, size), "        " )
					if show_data then
						if name == "ADD" then
							io.write(serialize_string(data_stream:read(size), true, utf8_data))
						else
							io.write(serialize_string(data_stream:read(1), true, utf8_data))
						end
					end
				end
			end
		end
		window_offset = window_offset + address_cache.here - (window_header.segment_length or 0)
		window_header = read_window_header(input)
		window_index = window_index + 1
	end
end

main(...)