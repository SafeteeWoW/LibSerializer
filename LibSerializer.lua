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

if not wipe then
	wipe = function(t)
		for k,_ in pairs(t) do
			t[k] = nil
		end
	end
end
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
local CH_SEPARATOR_LAST = strbyte(SEPARATOR_LAST)
local COMPRESSED_INT_BASE = 255 - strbyte("0") + 1

-- One byte string?
-- ASCII 1-10, 26-31, 248, 249, 250, 251, 252, 253, 254, 255
-- For string replacment
local strIndexSer = 0
local strToIndex = {}
local indexToStr = {}
local counts = {}
local key_counts = {}
local baseItemStringDecode = nil

-- Serialization functions
local function SerializeStringHelper(ch)	-- Used by SerializeValue for strings
	local n = strbyte(ch)
	if ch == ESCAPE or (SEPARATOR_FIRST <= ch and ch <= SEPARATOR_LAST) then
		return ESCAPE..strchar(n+47)
	else
		return ch
	end
end

local function IsTableArray(t)
	local len = #t
	local count = 0
	for k, v in pairs(t) do
		if type(k) ~= "number" then
			return false
		end
		if k < 1 or k > len or k ~= math.floor(k) then
			return false
		end
		count = count + 1
		if count > len then
			return false
		end
	end
	if count ~= len then
		return false
	else
		return true
	end
end

-- Preprocess the value to get duplicate strings/number count
local function GetValueCounts(val)
	-- We use "^" as a value separator, followed by one byte for type indicator
	local t = type(val)

	if t == "string" then
		counts[val] = counts[val] and counts[val] + 1 or 1
	elseif t == "number" then
		counts[val] = counts[val] and counts[val] + 1 or 1
	elseif t == "table" then	-- ^T...^t = table (list of key,value pairs)
		for k, v in pairs(val) do
			if type(k) == "string" then
				key_counts[k] = key_counts[k] and key_counts[k] + 1 or 1
			end
			GetValueCounts(k)
			GetValueCounts(v)
		end
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

local MARK_TABLE_END = {}

local serializeTbl = { } -- Unlike AceSerializer-3.0, there is no header in the serialized string.

--- Serialize the data passed into the function.
-- Takes a list of values (strings, numbers, booleans, nils, tables)
-- and returns it in serialized form (a string).\\
-- May throw errors on invalid data types.
-- @param ... List of values to serialize
-- @return The data in its serialized form (string)
function LibSerializer:Serialize(...)
	strIndexSer = 1
	wipe(strToIndex)
	wipe(counts)
	baseItemStringDecode = nil

	for i=1, select("#", ...) do
		local v = select(i, ...)
		GetValueCounts(v)
	end

	local stack = {}
	local stack_size = 0
	for i=select("#", ...), 1, -1 do
		local v = select(i, ...)
		stack_size = stack_size + 1
		stack[stack_size] = v
	end

	local res = {}
	local nres = 0
	while stack_size > 0 do
		local v = stack[stack_size]
		stack_size = stack_size - 1
		local t = type(v)
		if v == MARK_TABLE_END then
			nres = nres + 1
			res[nres] = SEPARATOR_TABLE_END
		elseif t == "string" then		-- ^S = string (escaped to remove nonprints, "^"s, etc)
			if not strToIndex[v] then
				if counts[v] > 1 and v:len() > tostring(strIndexSer):len() then
					res[nres+1] = SEPARATOR_STRING_REUSED
					res[nres+2] = gsub(v, ".", SerializeStringHelper)
					nres = nres + 2
					strToIndex[v] = strIndexSer
					strIndexSer = strIndexSer + 1
				else
					res[nres+1] = SEPARATOR_STRING
					res[nres+2] = gsub(v, ".", SerializeStringHelper)
					nres = nres + 2
				end
			else
				res[nres+1] = SEPARATOR_STRING_REPLACEMENT
				res[nres+2] = IntToBase224(strToIndex[v])
				nres = nres + 2
			end

		elseif t=="number" then
			if v ~= v then -- Not a Number (NaN)
				error ("Cannot serialize NaN")
			elseif v == inf then
				nres = nres + 1
				res[nres] = SEPARATOR_INTEGER
				nres = nres + 1
				res[nres] = string.char(32) -- WARNING: Assuming base 224 number cant start with 0 (ASCII 32)
			elseif v == -inf then
				nres = nres + 1
				res[nres] = SEPARATOR_INTEGER
				nres = nres + 1
				res[nres] = string.char(32+112)  -- WARNING: Assuming base 224 number cant start with -0 (ASCII 32+112)
			elseif v % 1 == 0 and v > -2^52 and v < 2^52 then
				-- Integer not in this ranged does not support precise
				-- integer computation
				-- TODO: Lua 5.3 int handling
				-- TODO: Better edge testing.
				nres = nres + 1
				res[nres] = SEPARATOR_INTEGER
				nres = nres + 1
				res[nres] = IntToBase224(v, true)
			else -- float number
				-- TODO: for Lua 5.3, need to consider
				-- "float" typed number is integer.
				local m, e = math_frexp(v)

				while m % 1 ~= 0 do
					m = m * 2
					e = e - 1
				end
				if e == 0 then
					nres = nres + 1
					res[nres] = SEPARATOR_FLOAT
					nres = nres + 1
					res[nres] = IntToBase224(m, true)
					nres = nres + 1
					res[nres] = string.char(32)
				else
					local encoded_exp = IntToBase224(e, true)
					for _=1, encoded_exp:len() do
						nres = nres + 1
						res[nres] = SEPARATOR_FLOAT
					end
					nres = nres + 1
					res[nres] = IntToBase224(m, true)
					nres = nres + 1
					res[nres] = encoded_exp
				end
			end

		elseif t=="table" then	-- ^T...^t = table (list of key,value pairs)
			local isArray = IsTableArray(v)
			if isArray then
				nres=nres+1
				res[nres] = SEPARATOR_ARRAY_START
				stack_size = stack_size + 1
				stack[stack_size] = MARK_TABLE_END
				for k=#v, 1, -1 do -- Key is not serilaized for array
					stack_size = stack_size + 1
					stack[stack_size] = v[k]
				end
			else
				nres=nres+1
				res[nres] = SEPARATOR_TABLE_START
				stack_size = stack_size + 1
				stack[stack_size] = MARK_TABLE_END
				for k, v in pairs(v) do -- Key is not serilaized for array
					stack_size = stack_size + 1
					stack[stack_size] = v
					stack_size = stack_size + 1
					stack[stack_size] = k
				end
			end

		elseif t=="boolean" then	-- ^B = true, ^b = false
			nres=nres+1
			if v then
				res[nres] = SEPARATOR_TRUE	-- true
			else
				res[nres] = SEPARATOR_FALSE	-- false
			end

		elseif t=="nil" then		-- ^Z = nil (zero, "N" was taken :P)
			nres=nres+1
			res[nres] = SEPARATOR_NIL
		else
			error(MAJOR..": Cannot serialize a value of type '"..t.."'")	-- can't produce error on right level, this is wildly recursive
		end
	end

	return tconcat(res, "", 1, nres)
end

-- Deserialization functions
local function DeserializeStringHelper(escape)
	local n = strbyte(escape, 2, 2)
	n = n - 47
	local ch = strchar(n)
	if ch == ESCAPE or (SEPARATOR_FIRST <= ch and ch <= SEPARATOR_LAST) then
		return ch
	else
		error("DeserializeStringHelper got called for '"..escape.."'?!?")  -- can't be reached unless regex is screwed up
	end
end

-- DeserializeValue: worker function for :Deserialize()
-- It works in two modes:
--   Main (top-level) mode: Deserialize a list of values and return them all
--   Recursive (table) mode: Deserialize only a single value (_may_ of course be another table with lots of subvalues in it)
--
-- The function _always_ works recursively due to having to build a list of values to return
--
-- Callers are expected to pcall(DeserializeValue) to trap errors

local function DeserializeValue(iter)
	local root_table = {}
	local table_stack = {root_table}
	local table_key = {1}
	local table_is_array = {true}
	local table_stack_size = 1
	local cur_table = root_table
	local cur_key = 1
	local cur_is_array = true

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
		elseif ctl == SEPARATOR_TRUE then	-- yeah yeah ignore data portion
			res = true
			if data ~= "" then
				error("Unexpected data for LibSerializer after true marker")
			end
		elseif ctl == SEPARATOR_FALSE then   -- yeah yeah ignore data portion
			res = false
			if data ~= "" then
				error("Unexpected data for LibSerializer after false marker")
			end
		elseif ctl == SEPARATOR_NIL then	-- yeah yeah ignore data portion
			res = nil
			if data ~= "" then
				error("Unexpected data for LibSerializer after nil marker")
			end
		elseif ctl == SEPARATOR_TABLE_START then
			res = {}
		elseif ctl == SEPARATOR_ARRAY_START then
			res = {}
		elseif ctl == SEPARATOR_TABLE_END then
			table_stack_size = table_stack_size - 1
			cur_table = table_stack[table_stack_size]
			cur_is_array = 	table_is_array[table_stack_size]
			cur_key = table_key[table_stack_size]
			if table_stack_size == 0 then
				error("TODO")
			end
		else
			error("Invalid LibSerializer control code '"..ctl.."'(".."character number code:"..strbyte(ctl)..")")
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
	strIndexDeser = 1
	baseItemStringDecode = nil
	wipe(indexToStr)
	local STR_END = SEPARATOR_INTEGER.."END"
	local iter = gmatch(str..STR_END, "(["..SEPARATOR_FIRST.."-"..SEPARATOR_LAST.."])([^"..SEPARATOR_FIRST.."-"..SEPARATOR_LAST.."]*)")
	return pcall(DeserializeValue, iter)
end

----------------------------------------
-- Base library stuff
----------------------------------------

LibSerializer.internals = {	-- for test scripts
	SerializeStringHelper = SerializeStringHelper,
	IntToCompressedInt = IntToCompressedInt,
	CompressedIntToInt = CompressedIntToInt,
}

local mixins = {
	"Serialize",
	"Deserialize",
}

LibSerializer.embeds = LibSerializer.embeds or {}

function LibSerializer:Embed(target)
	for k, v in pairs(mixins) do
		target[v] = self[v]
	end
	self.embeds[target] = true
	return target
end

-- Update embeds
for target, v in pairs(LibSerializer.embeds) do
	LibSerializer:Embed(target)
end

return LibSerializer