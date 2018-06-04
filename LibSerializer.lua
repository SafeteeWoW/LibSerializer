--- Development of **LibSerializer-3.0**. Modified from **LibSerializer-3.0**
-- The goal of this serializer is to use less space after compressed by LibCompress,
-- but the serialized string has less readability.
--
-- Copyright claim of **AceSerialzier-3.0
--[[
Copyright (c) 2007, Ace3 Development Team

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice,
      this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice,
      this list of conditions and the following disclaimer in the documentation
      and/or other materials provided with the distribution.
    * Redistribution of a stand alone version is strictly prohibited without
      prior written authorization from the Lead of the Ace3 Development Team.
    * Neither the name of the Ace3 Development Team nor the names of its contributors
      may be used to endorse or promote products derived from this software without
      specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
--]]

local MAJOR,MINOR = "LibSerializer-3.0", 1
local LibSerializer = {}

if not LibSerializer then return end

-- Lua APIs
local strbyte, strchar, gsub, gmatch, format = string.byte, string.char, string.gsub, string.gmatch, string.format
local assert, error, pcall = assert, error, pcall
local type, tostring, tonumber = type, tostring, tonumber
local pairs, ipairs, select, math_frexp, ldexp = pairs, ipairs, select, math.frexp, math.ldexp
local tconcat, tinsert = table.concat, table.insert
local floor = math.floor
local next = next

-- quick copies of string representations of wonky numbers
local inf = math.huge

-- separator characters for serializer.
-- Should replace these variable by constants for better performance later.
local ESCAPE = '\014' -- Escape character
local SEPARATOR_FIRST = '\015'
local SEPARATOR_STRING = '\015'	-- string
local SEPARATOR_INTEGER = '\016' -- Non floating number
local SEPARATOR_FLOAT = '\017' -- Mantissa part of floating number
local SEPARATOR_TABLE_START = '\018' -- Table starts
local SEPARATOR_TABLE_END = '\019' -- Table ends
local SEPARATOR_ARRAY_START = '\020' -- Array starts
local SEPARATOR_TRUE = '\021' -- true
local SEPARATOR_FALSE = '\022' -- false
local SEPARATOR_NIL = '\023' -- nil
local SEPARATOR_STRING_REPLACEMENT = '\024' -- For strings that are replaced (encoded as "reused string index")
local SEPARATOR_STRING_REUSED = '\025' -- For strings that are reused (encoded as original string)
local SEPARATOR_LAST = '\025'

-- One byte string?
-- ASCII 1-10, 26-31, 248, 249, 250, 251, 252, 253, 254, 255
-- For string replacment


-- Serialization functions
local serialize_pattern = "(["..ESCAPE.."-"..SEPARATOR_LAST.."])"
local SerializeStringHelper = {}
for i= 0, 255 do
	local ch = strchar(i)
	if ch == ESCAPE or (SEPARATOR_FIRST <= ch and ch <= SEPARATOR_LAST) then
		SerializeStringHelper[ch] =
			ESCAPE..strchar(i+32-strbyte(ESCAPE))
	end
end

local DeserializeStringHelper = {}
-- TODO: Error check when Escape follows an invalid character.

for i= 0, 255 do
	local ch = strchar(i)
	if ch == ESCAPE or (SEPARATOR_FIRST <= ch and ch <= SEPARATOR_LAST) then
		DeserializeStringHelper[ESCAPE..strchar(i+32-strbyte(ESCAPE))] = ch
	end
end

local function IntToBase224(n, is_signed)
	assert(n%1==0)
	local non_negative = (n >= 0)
	if not non_negative then
		n = -n
	end
	local s = ""
	while (n ~= 0) do
		local digit = n % 224
		n  = (n-digit)/224
		if (n == 0 and is_signed) then
			if (non_negative) then
				if digit < 112 then
					s = s..string.char(digit+32)
				else
					s = s..string.char(digit+32)..string.char(32)
				end
			else
				if digit < 112 then
					s = s..string.char(digit+112+32)
				else
					s = s..string.char(digit+32)..string.char(112+32)
				end
			end
		else
			if digit + 32 >= 256 then
				print("WTF", digit)
			end
			s = s..string.char(digit+32)
		end
	end
	return s
end

local function Base224ToInt(s, is_signed)
	local n = 0
	local base = 1
	local len = #s
	local is_negative = false
	for i=1, len do
		local digit = string.byte(s, i) - 32
		if digit < 0 then
			error("wrong digit")
		end
		if is_signed and i == len then
			if digit >= 112 then
				is_negative = true
				digit = digit - 112
			end
		end
		n = n + digit * base
		base = base * 224
		if is_negative then
			n = -n
		end
	end
	return n
end

local function SortTable2ndDecreasing(a, b)
	return a[2] > b[2] or (a[2] == b[2] and a[1] < b[1])
end

local _NIL = {}
--- Serialize the data passed into the function.
-- Takes a list of values (strings, numbers, booleans, nils, tables)
-- and returns it in serialized form (a string).\\
-- May throw errors on invalid data types.
-- @param ... List of values to serialize
-- @return The data in its serialized form (string)
function LibSerializer:Serialize(...)
	local strIndexSer = 1
	local strToIndex = {}
	local counts = {}
	local key_counts = {}

	local root_table = {...}
	local cur_table = root_table
	local table_stack_size = 1
	local table_stack = {cur_table}
	local table_cur_key = {}
	local table_next_val = {}
	local table_is_array = {}
	local table_sorted_keys = {}
	table_is_array[cur_table] = 0

	-- TODO: Clean up my messy code.
	while table_stack_size > 0 do
		local k = table_cur_key[table_stack_size]
		local v
		local table_size = #cur_table
		local table_count = table_is_array[cur_table]
		local sorted_keys = table_sorted_keys[cur_table] or {}
		local val = table_next_val[table_stack_size]
		local next_val
		local val_is_key, next_val_is_key
		if val == nil then
			k, v = next(cur_table, k)
			val, next_val = k, v
			val_is_key, next_val_is_key = true, false
		end
		while k ~= nil do
			while val ~= nil do
				local type_val = type(val)
				if val_is_key then
					if cur_table ~= root_table then
						sorted_keys[#sorted_keys+1] = val
					end
					if table_count then
						if type_val ~= "number" then
							table_count = nil
						elseif val < 1 or val > table_size or val % 1 ~= 0 then
							table_count = nil
						else
							table_count = table_count + 1
						end
					end
				end
				if type_val== "string" then
					counts[val] = (counts[val] or 0) + 1
					if val_is_key then
						key_counts[val] = (key_counts[val] or 0) + 1
					end
				elseif type_val == "table" then
					table_cur_key[table_stack_size] = k
					table_next_val[table_stack_size] = next_val
					table_is_array[cur_table] = table_count
					table_sorted_keys[cur_table] = sorted_keys
					sorted_keys = {}
					table_stack_size = table_stack_size + 1
					cur_table = val
					table_size = #cur_table
					table_stack[table_stack_size] = cur_table
					k = nil
					next_val = nil
					table_count = 0
				end
				val, next_val = next_val, nil
				val_is_key, next_val_is_key = next_val_is_key, nil
			end -- while val ~= nil
			k, v = next(cur_table, k)
			val, next_val = k, v
			val_is_key, next_val_is_key = true, false
		end -- while k ~= nil
		if table_count == table_size then
			table_is_array[cur_table] = true
			table_sorted_keys[cur_table] = nil
		else
			table_is_array[cur_table] = nil
			table_sorted_keys[cur_table] = sorted_keys
		end
		table_stack_size = table_stack_size - 1
		cur_table = table_stack[table_stack_size]
	end

	local sort_key = {}
	local sort_key_tblsize = 0
	for k, v in pairs(key_counts) do
		if v > 1 then
			sort_key_tblsize = sort_key_tblsize + 1
			sort_key[sort_key_tblsize] = {k, v}
		end
	end
	table.sort(sort_key, SortTable2ndDecreasing)

	local duplicate_keys = {}
	local duplicate_keys_to_index = {}
	local duplicate_keys_tblsize = sort_key_tblsize
	for i = 1, duplicate_keys_tblsize do
		local t = sort_key[i]
		duplicate_keys[i] = t[2]
		duplicate_keys_to_index[t[1]] = i
	end

	local type_order = {
		["string"] = 1,
		["number"] = 2,
		["table"] = 3,
		["boolean"] = 4,
	}

	local function SortTableKeys(a, b)
		local type_a = type(a) or 10000
		local type_b = type(b) or 10000
		local type_order_a = type_order[type_a]
		local type_order_b = type_order[type_b]

		if type_order_a ~= type_order_b then
			return type_order_a < type_order_b
		elseif type_a == "string" then
			local order_a = duplicate_keys_to_index[a] or math.huge
			local order_b = duplicate_keys_to_index[b] or math.huge
			if order_a ~= order_b then
				return order_a > order_b
			else
				return a < b
			end
		elseif type_a == "number" then
			local is_float_a = (a % 1 == 0)
			local is_float_b = (b % 1 == 0)
			if is_float_a ~= is_float_b then
				return is_float_b
			else
				return a < b
			end
		else
			return tostring(a) < tostring(b)
		end
	end

	for _, sorted_keys in pairs(table_sorted_keys) do
		table.sort(sorted_keys, SortTableKeys)
	end
	sort_key = nil -- free memory space

	local res = {}
	local nres = 0
	cur_table = root_table
	table_stack_size = 1
	table_stack = {cur_table}
	table_cur_key = {0}
	table_next_val = {}

	if next(duplicate_keys) then
		root_table[0] = duplicate_keys
		table_cur_key[1] = -1
		table_is_array[duplicate_keys] = true
	end
	table_is_array[root_table] = true

	if select("#", ...) == 0 then
		root_table[1] = _NIL
	else
		for i = 1, select("#", ...) do
			if root_table[i] == nil then
				root_table[i] = _NIL
			end
		end
	end

	while table_stack_size > 0 do
		local cur_table_is_array = table_is_array[cur_table]
		local cur_key = table_cur_key[table_stack_size]
		local cur_sorted_keys = table_sorted_keys[cur_table]

		local val = table_next_val[table_stack_size]
		local k, v
		if val == nil then
			cur_key = cur_key + 1
		end

		if cur_table_is_array then
			k, v = cur_key, cur_table[cur_key]
			if v == nil then k = nil end
		else
			k = cur_sorted_keys[cur_key]
			if k ~= nil then
				v = cur_table[k]
			end
		end

		while k ~= nil do
			local next_val
			if val == nil then
				if cur_table_is_array then
					val = v
					next_val = nil
				else
					val = k
					next_val = v
				end
			end

			while val ~= nil do
				nres = nres + 1
				local type_val = type(val)
				if type_val == "string" then
					if not strToIndex[val] then
						local index = IntToBase224(strIndexSer)
						local val_written = gsub(val, serialize_pattern
							, SerializeStringHelper)
						if counts[val] > 1 and #val_written > #index then
							res[nres] = SEPARATOR_STRING_REUSED
							nres = nres + 1
							res[nres] = val_written
							strToIndex[val] = index
							strIndexSer = strIndexSer + 1
						else
							res[nres] = SEPARATOR_STRING
							nres = nres + 1
							res[nres] = val_written
						end
					else
						res[nres] = SEPARATOR_STRING_REPLACEMENT
						nres = nres + 1
						res[nres] = strToIndex[val]
					end
				elseif type_val == "number" then
					if val ~= val then -- Not a Number (NaN)
						error ("Cannot serialize NaN")
					elseif val == inf then
						res[nres] = SEPARATOR_INTEGER
						nres = nres + 1
						res[nres] = string.char(32) -- WARNING: Assuming base 224 number cant start with 0 (ASCII 32)
					elseif val == -inf then
						res[nres] = SEPARATOR_INTEGER
						nres = nres + 1
						res[nres] = string.char(32+112)  -- WARNING: Assuming base 224 number cant start with -0 (ASCII 32+112)
					elseif val % 1 == 0 and val > -2^52 and val < 2^52 then
						-- Integer not in this ranged does not support precise
						-- integer computation
						-- TODO: Lua 5.3 int handling
						-- TODO: Better edge testing.
						res[nres] = SEPARATOR_INTEGER
						nres = nres + 1
						res[nres] = IntToBase224(val, true)
					else -- float number
						-- TODO: for Lua 5.3, need to consider
						-- "float" typed number is integer.
						local m, e = math_frexp(val)

						while m % 1 ~= 0 do
							m = m * 2
							e = e - 1
						end
						if e == 0 then
							res[nres] = SEPARATOR_FLOAT
							nres = nres + 1
							res[nres] = IntToBase224(m, true)
							nres = nres + 1
							res[nres] = string.char(32)
						else
							local encoded_exp = IntToBase224(e, true)
							for _=1, #encoded_exp do
								res[nres] = SEPARATOR_FLOAT
								nres = nres + 1
							end
							res[nres] = IntToBase224(m, true)
							nres = nres + 1
							res[nres] = encoded_exp
						end
					end
				elseif val == _NIL then
					res[nres] = SEPARATOR_NIL
				elseif val == true then
					res[nres] = SEPARATOR_TRUE
				elseif val == false then
					res[nres] = SEPARATOR_FALSE
				elseif type_val == "table" then
					table_cur_key[table_stack_size] = cur_key
					table_next_val[table_stack_size] = next_val
					cur_table = val
					table_stack_size = table_stack_size + 1
					table_stack[table_stack_size] = cur_table
					cur_table_is_array = table_is_array[cur_table]
					cur_sorted_keys = table_sorted_keys[cur_table]

					if cur_table_is_array then
						cur_key = 0
						res[nres] = (val ~= duplicate_keys) and
							SEPARATOR_ARRAY_START or SEPARATOR_TABLE_END
					else
						cur_key = 0
						res[nres] = SEPARATOR_TABLE_START
					end
					next_val = nil
				else
					-- can't produce error on right level, this is wildly recursive
					error(MAJOR..": Cannot serialize a value of type '"
						..type_val.."'")
				end

				val = next_val
				next_val = nil
			end -- while val ~= nil

			cur_key = cur_key + 1
			if cur_table_is_array then
				k, v = cur_key, cur_table[cur_key]
				if v == nil then k = nil end
			else
				k = cur_sorted_keys[cur_key]
				if k ~= nil then
					v = cur_table[k]
				end
			end
		end -- while k ~= nil
		if table_stack_size > 1 then
			nres = nres + 1
			res[nres] = SEPARATOR_TABLE_END
		end
		table_stack_size = table_stack_size - 1
		cur_table = table_stack[table_stack_size]
	end -- while table_stack_size > 0

	return tconcat(res, "", 1, nres)
end

local function DeserializeValue(iter)
	local indexToStr = {}
	local strIndexDeser = 1

	local root_table = {}
	local table_stack = {root_table}
	local table_key = {1}
	local table_is_array = {true}
	local table_stack_size = 1
	local cur_table = root_table
	local cur_key = 1
	local cur_is_array = true
	local duplicate_keys

	while true do
		local ctl, data = iter()
		if not ctl then
			error("ilformed data for LibSerializer")
		end

		local res
		if ctl == SEPARATOR_STRING then
			res = gsub(data, ESCAPE..".", DeserializeStringHelper)
		elseif ctl == SEPARATOR_STRING_REUSED then
			res = gsub(data, ESCAPE..".", DeserializeStringHelper)
			indexToStr[strIndexDeser] = res
			strIndexDeser = strIndexDeser + 1
		elseif ctl == SEPARATOR_STRING_REPLACEMENT then
			local index = Base224ToInt(data)
			if not index or not indexToStr[index] then
				error("Invalid string replacement index in LibSerializer")
			end
			res = indexToStr[index]
		elseif ctl == SEPARATOR_INTEGER then
			if data == "END" then -- End of string mark -- TODO
				break
			end
			if data == string.char(32) then
				res = inf
			elseif data == string.char(32+112) then
				res = -inf
			else
				res = Base224ToInt(data, true)
			end
			if not res then
				error("Invalid serialized number: '"..tostring(data).."'")
			end
		elseif ctl == SEPARATOR_FLOAT then     -- ^F<mantissa>^f<exponent>
			local exp_strlen = 1
			while data == "" and exp_strlen < 4 do
				ctl, data = iter()
				exp_strlen = exp_strlen + 1
				if ctl ~= SEPARATOR_FLOAT then
					error ("TODO")
				end
			end
			if exp_strlen == 4 then
				error("TODO3")
			end
			local len = data:len()
			if len < exp_strlen then
				error ("TODO2")
			end
			local m = Base224ToInt(data:sub(1, len-exp_strlen), true)
			local e = Base224ToInt(data:sub(len-exp_strlen+1, len), true)
			res = m*(2^e)
		elseif ctl == SEPARATOR_TRUE then
			res = true
			if data ~= "" then
				error("Unexpected data for LibSerializer after true marker")
			end
		elseif ctl == SEPARATOR_FALSE then
			res = false
			if data ~= "" then
				error("Unexpected data for LibSerializer after false marker")
			end
		elseif ctl == SEPARATOR_NIL then
			res = nil
			if data ~= "" then
				error("Unexpected data for LibSerializer after nil marker")
			end
		elseif ctl == SEPARATOR_TABLE_START then
			res = {}
		elseif ctl == SEPARATOR_ARRAY_START then
			res = {}
		elseif ctl == SEPARATOR_TABLE_END then
			if (table_stack_size == 1
					and not duplicate_keys) then
				duplicate_keys = {}
				table_key[table_stack_size] = cur_key
				cur_table = duplicate_keys
				table_stack_size = table_stack_size + 1
				table_stack[table_stack_size] = cur_table
				cur_key = 1
			else
				table_stack_size = table_stack_size - 1
				cur_table = table_stack[table_stack_size]
				cur_is_array = 	table_is_array[table_stack_size]
				cur_key = table_key[table_stack_size]
				if table_stack_size == 0 then
					error("TODO. wrong table end mark")
				end
			end
		else
			error("Invalid LibSerializer control code '"..ctl
				.."'(".."character number code:"..strbyte(ctl)..")")
		end

		if ctl ~= SEPARATOR_TABLE_END then
			if cur_is_array then
				cur_table[cur_key] = res
				cur_key = cur_key + 1
			else
				if cur_key ~= nil then
					cur_table[cur_key] = res
					cur_key = nil
				else
					cur_key = res
					if cur_key == nil then
						error ("nil table key")
					end
				end
			end

			if ctl == SEPARATOR_TABLE_START then
				table_key[table_stack_size] = cur_key
				cur_table = res
				table_stack_size = table_stack_size + 1
				table_stack[table_stack_size] = cur_table
				table_is_array[table_stack_size] = false
				cur_is_array = false
				cur_key = nil
			elseif ctl == SEPARATOR_ARRAY_START then
				table_key[table_stack_size] = cur_key
				cur_table = res
				table_stack_size = table_stack_size + 1
				table_stack[table_stack_size] = cur_table
				table_is_array[table_stack_size] = true
				cur_is_array = true
				cur_key = 1
			end
		end
	end

	if table_stack_size > 1 then
		error ("TODO: Unmatch table")
	end
	return unpack(root_table)
end

--- Deserializes the data into its original values.
-- Accepts serialized data, ignoring all control characters and whitespace.
-- @param str The serialized data (from :Serialize)
-- @return true followed by a list of values, OR false followed by an error message
function LibSerializer:Deserialize(str)
	local STR_END = SEPARATOR_INTEGER.."END"
	local iter = gmatch(str..STR_END, "(["..SEPARATOR_FIRST.."-"
		..SEPARATOR_LAST.."])([^"..SEPARATOR_FIRST.."-"..SEPARATOR_LAST.."]*)")
	return pcall(DeserializeValue, iter)
end

----------------------------------------
-- Base library stuff
----------------------------------------

LibSerializer.internals = {	-- for test scripts
}

local mixins = {
	"Serialize",
	"Deserialize",
}

LibSerializer.embeds = LibSerializer.embeds or {}

function LibSerializer:Embed(target)
	for _, v in pairs(mixins) do
		target[v] = self[v]
	end
	self.embeds[target] = true
	return target
end

-- Update embeds
for target, _ in pairs(LibSerializer.embeds) do
	LibSerializer:Embed(target)
end

return LibSerializer