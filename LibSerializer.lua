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
local pairs, ipairs, select, frexp, ldexp = pairs, ipairs, select, math.frexp, math.ldexp
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

local serNaN  -- can't do this in 4.3, see ace3 ticket 268
local serInf, serInfMac = "1.#INF", "inf"
local serNegInf, serNegInfMac = "-1.#INF", "-inf"

-- separator characters for serializer.
-- Should replace these variable by constants for better performance later.
local ESCAPE = '\001' -- Escape character
local SEPARATOR_FIRST = '\002'
local SEPARATOR_STRING = '\002'	-- string
local SEPARATOR_NUMBER = '\003' -- Non floating number
local SEPARATOR_FLOAT_MAN = '\004' -- Mantissa part of floating number
local SEPARATOR_FLOAT_EXP = '\005' -- Exponent part of floating number
local SEPARATOR_TABLE_START = '\006' -- Table starts
local SEPARATOR_TABLE_END = '\007' -- Table ends
local SEPARATOR_ARRAY_START = '\008' -- Array starts
local SEPARATOR_TRUE = '\009' -- true
local SEPARATOR_FALSE = '\010' -- false
local SEPARATOR_NIL = '\011' -- nil
local SEPARATOR_STRING_REPLACEMENT = '\012' -- For strings that are replaced (encoded as "reused string index")
local SEPARATOR_STRING_REUSED = '\013' -- For strings that are reused (encoded as original string)
local SEPARATOR_LAST = '\013'
local CH_SEPARATOR_LAST = strbyte(SEPARATOR_LAST)
local COMPRESSED_INT_BASE = 255 - strbyte("0") + 1

-- For string replacment
local strIndexSer = 0
local strToIndex = {}
local indexToStr = {}
local counts = {}
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
local function GetValueCounts(v)
	-- We use "^" as a value separator, followed by one byte for type indicator
	local t = type(v)

	if t == "string" then
		counts[v] = counts[v] and counts[v] + 1 or 1
	elseif t == "number" then
		counts[v] = counts[v] and counts[v] + 1 or 1
	elseif t == "table" then	-- ^T...^t = table (list of key,value pairs)
		for k, v in pairs(v) do
			nres = GetValueCounts( k)
			nres = GetValueCounts(v)
		end
	end
end

local function IntToCompressedInt(int)
	local t = {}
	if int == 0 then
		return strchar(48)
	else
		while int > 0 do
			local rem = int % COMPRESSED_INT_BASE
			int = floor(int / COMPRESSED_INT_BASE)
			local ch = strchar(rem + 48)
			tinsert(t, 1, ch)
		end
		return tconcat(t)
	end
end

local function CompressedIntToInt(cInt)
	local int = 0
	local multiplier = 1
	for i=cInt:len(), 1, -1 do
		local n = strbyte(cInt, i) - 48
		int = int + n * multiplier
		multiplier = multiplier * COMPRESSED_INT_BASE
	end
	return int
end

local function EncodeItemString(values)
	local s = {}
	for _, v in ipairs(values) do
		if v == 0 then
			tinsert(s, "")
		elseif v > 0 then
			tinsert(s, tostring(v*2))
		else
			tinsert(s, tostring((math.abs(v))*2+1))
		end
	end
	return tconcat(s, ":")
end

local function DecodeItemString(itemString)
	local values = {}
	for v in itemString:gmatch(":(-?[0-9]*)") do
		if v == "" then
			tinsert(values, 0)
		else
			local n = tonumber(v)
			if n % 2 == 0 then
				tinsert(values, tonumber(n/2))
			else
				tinsert(values, -tonumber((v-1)/2))
			end

		end
	end
	return values
end

local function SerializeValue(v, res, nres)
	-- We use "^" as a value separator, followed by one byte for type indicator
	local t = type(v)

	if t == "string" then		-- ^S = string (escaped to remove nonprints, "^"s, etc)
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
			res[nres+2] = IntToCompressedInt(strToIndex[v])
			nres = nres + 2
		end

	elseif t=="number" then	-- ^N = number (just tostring()ed) or ^F (float components)
		local str = tostring(v)
		if tonumber(str) == v  --[[not in 4.3 or str==serNaN]] then
			local oldStr = str
			-- translates just fine, transmit as-is
			res[nres+1] = SEPARATOR_NUMBER
			-- Another optimization. Transform the number with the form "0.7" to "07"
			res[nres+2] = tonumber(str)
			--if oldStr ~= res[nres+2] then print(oldStr, res[nres+2]) end
			nres = nres + 2
		elseif v == inf or v == -inf then
			res[nres+1] = SEPARATOR_NUMBER
			res[nres+2] = v == inf and serInf or serNegInf
			nres = nres + 2
		else
			local m, e = frexp(v)
			res[nres+1] = SEPARATOR_FLOAT_MAN
			res[nres+2] = format("%.0f", m * 2 ^ 53)	-- force mantissa to become integer (it's originally 0.5--0.9999)
			res[nres+3] = SEPARATOR_FLOAT_EXP
			res[nres+4] = tostring(e - 53)
			nres = nres + 4
		end

	elseif t=="table" then	-- ^T...^t = table (list of key,value pairs)
		local isArray = IsTableArray(v)
		if isArray then
			nres=nres+1
			res[nres] = SEPARATOR_ARRAY_START
			for _, v in ipairs(v) do -- Key is not serilaized for array
				nres = SerializeValue(v, res, nres)
			end
			nres=nres+1
			res[nres] = SEPARATOR_TABLE_END
		else
			nres=nres+1
			res[nres] = SEPARATOR_TABLE_START
			for k,v in pairs(v) do
				nres = SerializeValue(k, res, nres)
				nres = SerializeValue(v, res, nres)
			end
			nres=nres+1
			res[nres] = SEPARATOR_TABLE_END
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

	return nres
end



local serializeTbl = { } -- Unlike AceSerializer-3.0, there is no header in the serialized string.

--- Serialize the data passed into the function.
-- Takes a list of values (strings, numbers, booleans, nils, tables)
-- and returns it in serialized form (a string).\\
-- May throw errors on invalid data types.
-- @param ... List of values to serialize
-- @return The data in its serialized form (string)
function LibSerializer:Serialize(...)
	local nres = 0
	strIndexSer = 1
	wipe(strToIndex)
	wipe(counts)
	baseItemStringDecode = nil

	for i=1, select("#", ...) do
		local v = select(i, ...)
		GetValueCounts(v)
	end

	for i=1, select("#", ...) do
		local v = select(i, ...)
		nres = SerializeValue(v, serializeTbl, nres)
	end

	return tconcat(serializeTbl, "", 1, nres)
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

local function DeserializeNumberHelper(number)
	--[[ not in 4.3 if number == serNaN then
		return 0/0
	else]]if number == serNegInf or number == serNegInfMac then
		return -inf
	elseif number == serInf or number == serInfMac then
		return inf
	else
		return tonumber(number)
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

local function DeserializeValue(iter, single, ctl, data)
	if not single then
		ctl, data = iter()
	end

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
		local index = CompressedIntToInt(data)
		if not index or not indexToStr[index] then
			error("Invalid string replacement index in LibSerializer")
		end
		res = indexToStr[index]
	elseif ctl == SEPARATOR_NUMBER then
		if data == "END" then -- End of string mark
			return
		end
		res = DeserializeNumberHelper(data)
		if not res then
			error("Invalid serialized number: '"..tostring(data).."'")
		end
	elseif ctl == SEPARATOR_FLOAT_MAN then     -- ^F<mantissa>^f<exponent>
		local ctl2, e = iter()
		if ctl2 ~= SEPARATOR_FLOAT_EXP then
			error("Invalid serialized floating-point number")
		end
		local m = tonumber(data)
		e = tonumber(e)
		if not (m and e) then
			error("Invalid serialized floating-point number, expected mantissa and exponent, got '"..tostring("0."..m).."' and '"..tostring(e).."'")
		end
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
		-- ignore ^T's data, future extensibility?
		res = {}
		local k,v
		while true do
			ctl, data = iter()
			if ctl == SEPARATOR_TABLE_END then
				if data ~= "" then
					error("Unexpected data for LibSerializer after table end marker")
				end
				break
			end
			k = DeserializeValue(iter, true, ctl, data)
			if k==nil then
				error("Invalid LibSerializer table format (no table end marker)")
			end
			ctl, data = iter()
			v = DeserializeValue(iter, true, ctl, data)
			if v == nil then
				error("Invalid LibSerializer table format (no table end marker)")
			end
			res[k] = v
		end
	elseif ctl == SEPARATOR_ARRAY_START then
		-- ignore ^T's data, future extensibility?
		res = {}
		local k = 1
		while true do
			ctl, data = iter()
			if ctl == SEPARATOR_TABLE_END then
				if data ~= "" then
					error("Unexpected data for LibSerializer after array end marker")
				end
				break
			end
			local v = DeserializeValue(iter, true, ctl, data)
			if v == nil then
				error("Invalid LibSerializer table format (no table end marker)")
			end
			res[k] = v
			k = k + 1
		end
	else
		error("Invalid LibSerializer control code '"..ctl.."'(".."character number code:"..strbyte(ctl)..")")
	end

	if not single then
		return res, DeserializeValue(iter)
	else
		return res
	end
end

--- Deserializes the data into its original values.
-- Accepts serialized data, ignoring all control characters and whitespace.
-- @param str The serialized data (from :Serialize)
-- @return true followed by a list of values, OR false followed by an error message
function LibSerializer:Deserialize(str)
	strIndexDeser = 1
	baseItemStringDecode = nil
	wipe(indexToStr)
	local STR_END = SEPARATOR_NUMBER.."END"
	local iter = gmatch(str..STR_END, "(["..SEPARATOR_FIRST.."-"..SEPARATOR_LAST.."])([^"..SEPARATOR_FIRST.."-"..SEPARATOR_LAST.."]*)")
	return pcall(DeserializeValue, iter)
end

----------------------------------------
-- Base library stuff
----------------------------------------

LibSerializer.internals = {	-- for test scripts
	SerializeValue = SerializeValue,
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