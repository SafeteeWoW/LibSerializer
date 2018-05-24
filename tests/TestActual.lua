package.path = package.path..";../?.lua"..";?.lua"
local LibSerializer = require("LibSerializer")
local AceSerializer = require("AceSerializer")

local weakaura_ser_ace3_file = io.open("tests/reference/WeakAurasDecoded.txt"
, "rb")

local weakaura_ser_ace3 = weakaura_ser_ace3_file:read("*all")

print(weakaura_ser_ace3:len())
print("-----------------------")

local _, t = AceSerializer:Deserialize(weakaura_ser_ace3)

local weakaura_ser_lib = LibSerializer:Serialize(t)
print(weakaura_ser_lib:len())

local LibDeflate = require("LibDeflate")

print(LibDeflate:CompressDeflate(weakaura_ser_ace3, {level = 9}):len())

print(LibDeflate:CompressDeflate(weakaura_ser_lib, {level = 9}):len())