package.path = package.path..";../?.lua;?.lua"

local lu = require("luaunit")

local Lib = require("LibSerializer")
local LibAce = require("tests/AceSerializer")
local LibDeflate = require("LibDeflate")

local assert = assert
local tostring = tostring
local string_char = string.char
local string_byte = string.byte
local table_concat = table.concat
local table_insert = table.insert
local math_random = math.random
local unpack = unpack or table.unpack
local select = select

-- Dont like real random. I need bug reproducablity.
math.randomseed(0)
-- Get a random string with at least 256 len which includes all characters
local function GetRandomStringUniqueChars(strlen)
	local taken = {}
	local tmp = {}
	for i=0, (strlen < 256) and strlen-1 or 255 do
		local rand = math_random(1, 256-i)
		local count = 0
		for j=0, 255 do
			if (not taken[j]) then
				count = count + 1
			end
			if count == rand then
				taken[j] = true
				tmp[#tmp+1] = string_char(j)
				break
			end
		end
	end
	if strlen > 256 then
		for _=1, strlen-256 do
			table_insert(tmp, math_random(1, #tmp+1)
				, string_char(math_random(0, 255)))
		end
	end
	return table_concat(tmp)
end
assert(GetRandomStringUniqueChars(3):len() == 3)
assert(GetRandomStringUniqueChars(255):len() == 255)
assert(GetRandomStringUniqueChars(256):len() == 256)
assert(GetRandomStringUniqueChars(500):len() == 500)
do
	local taken = {}
	local str = GetRandomStringUniqueChars(256)
	for i=1, 256 do
		local byte = string_byte(str, i, i)
		assert(not taken[byte])
		taken[byte] = true
	end
end

local function Test(...)
	local result = {Lib:Deserialize(Lib:Serialize(...))}
	local msg = ""
	if select(1, ...) ~= nil then
		msg = tostring(select(1, ...))
	end
	lu.assertEquals(result, {result[1], ...}, msg)
	lu.assertTrue(result[1])
end

local total_lib = 0
local total_ace = 0
local function TestReference(filename)
	local file = io.open(filename, "rb")
	lu.assertNotNil(file)
	local data = file:read("*all")
	file:close()
	local result = {LibAce:Deserialize(data)}
	lu.assertTrue(result[1])
	local to_ser = {select(2, result)}
	Test(unpack(to_ser))

	local lib_data = Lib:Serialize(select(2, LibAce:Deserialize(data)))
	local libace_compress = LibDeflate:CompressDeflate(data, {level = 9})
	local lib_compress = LibDeflate:CompressDeflate(lib_data, {level=9})

	total_lib = total_lib + lib_compress:len()
	total_ace = total_ace + libace_compress:len()
	print(("%.4f, %.4f | %d, %d | %d, %d"):format(total_lib/total_ace
		, lib_compress:len()/libace_compress:len(),
		lib_compress:len(), libace_compress:len(), lib_data:len(), data:len()))
end


TestBasicTypes = {}
	function TestBasicTypes:TestEmpty()
		Test("")
	end
	function TestBasicTypes:TestIntegers()
		for i=-1000, 1000 do
			Test(tostring(i))
		end
	end
	function TestBasicTypes:TestTrue()
		Test(true)
	end
	function TestBasicTypes:TestFalse()
		Test(false)
	end
	function TestBasicTypes:TestNil()
		Test(nil)
	end
	function TestBasicTypes:TestFloat()
		for i=-256, 256 do
			for j = -256, 256 do
				if j ~= 0 then
					Test(i/j)
				end
			end
		end
	end
	function TestBasicTypes:TestChar()
		for i = 0, 255 do
			Test(string_char(i))
		end
	end
	function TestBasicTypes:TestString()
		for _ = 1, 100 do
			Test(GetRandomStringUniqueChars(math.random(2, 600)))
		end
	end
	function TestBasicTypes:TestInf()
		Test(math.huge)
	end
	function TestBasicTypes:TestMinusInf()
		Test(-math.huge)
	end
	function TestBasicTypes:TestSmallExpFloat()
		Test(2^(-512))
		Test(3*2^(-513))
		Test(2^(-1000))
	end

	function TestBasicTypes:TestBigExpFloat()
		Test(2^(1000))
		Test(3^(500))
		Test(2.5^(750))
	end

TestFromAce3 = {}
	function TestFromAce3:TestStringBurning()
		for _=1,1000 do
			local str = string_byte(math_random(0,255))
				..string_byte(math_random(0,255))
				..string_byte(math_random(0,255))
				..string_byte(math_random(0,255))
			Test(str)
		end
		for _=1,1000 do
			local str = string_byte(math_random(0,255))
			..string_byte(math_random(0,255))
				..string_byte(math_random(0,255))
				..string_byte(math_random(0,255))
			Test(true, str)
		end
		for _=1,1000 do
			local str = string_byte(math_random(0,255))
				..string_byte(math_random(0,255))
				..string_byte(math_random(0,255))
				..string_byte(math_random(0,255))
			Test(5, str, true)
		end
	end
	function TestFromAce3:TestWildCombos1()
		Test(
			"firstval",
			123e-17,
			true,
			false,
			nil,
			{
				{
					foo="bar"
				},
				{
					baz={}
				},
				name="val",
			},
			"\001\032\127^~fin!^^"
		)
	end
	function TestFromAce3:TestWildCombos2()
		Test(
			{
				"firstval",
				123e-17,
				true,
				false,	-- ACE-130
				nil,
				{
					{
						foo="bar"
					},
					{
						baz={}
					},
					name="val",
				},
				"\001\032\127^~fin!^^",
				[true]="yes",
				[false]="no"	-- ACE-130
			}
		)
	end
	function TestFromAce3:TestSpecialNumbers()
		Test(1/3)
		Test(2/3)
		Test(math.pi)
		Test(math.exp(1))
		Test(math.sqrt(math.exp(1)))
		Test(math.sqrt(0.5))
	end
	function TestFromAce3:TestBananaDKP()
		local BananaDKP = {
			[""] = 0.474609375,
			["Sarene"] = 23.2291748046875,
			["Exatos"] = 6,
			["Skyfiah"] = 4,
			["N韊na"] = 5,
			["Azax"] = 102.08,
			["Korumo"] = 28.78446006774903,
			["Tarannon"] = 51.19950154685832,
			["Relinquish"] = 76.03103977709394,
			["Outofcontrol"] = 45.57863802415056,
			["Naryaa"] = 69.01798407067545,
			["Zakris"] = 7.3996074843177,
			["Exodous"] = 128.1306512626569,
			["Flirfull"] = 100.6661528351939,
			["Birdwings"] = 33.7216552734375,
			["Theoxis"] = 5,
			["Adior"] = 54.953125,
			["Vdgg"] = 4,
			["Positronics"] = 46.96747932434081,
			["Paces"] = 37.74374999999998,
			["R韔t"] = 14.9,
			["Kaostechno"] = 34.04490834849657,
			["Skrinky"] = 93.79947433816274,
			["Eezilla"] = 20.81249999999999,
			["Folk"] = 6,
			["Knaus"] = 22.596875,
			["Undeadangel"] = 44.78000434875492,
			["Purplerattii"] = 57.53351999828472,
			["Laloena"] = 55.53190727233888,
			["Druidturtle"] = 1.5,
			["Shiaq"] = 105.3250000000001,
			["Heavyx"] = 26.7,
			["Omgashammy"] = 174.3007940918701,
			["Vesira"] = 49.56464843750001,
			["Szentlovag"] = 31.47292669415476,
			["Moohawk"] = 90.65259001851082,
			["Kain"] = 124.6437499999999,
			["Ewandor"] = 8,
			["Molh"] = 19.10390625,
			["Shekowaffle"] = 61.71009125776505,
			["Nesitn"] = 4.5,
			["Spikyo"] = 41,
			["Winning"] = 6.5,
			["Soaz"] = 6.299999999999999,
			["Terezka"] = 88.11159490764035,
			["Palaxm"] = 18.06328125,
			["Purplemist"] = 16.68659827320444,
			["Fallirin"] = 38.675,
			["Deriyana"] = 7.5,
			["Tohil"] = 51.7,
			["Leksa"] = 13.475,
			["Guldy"] = 74.54692840576169,
			["Cryptos"] = 35.3587890625,
			["Weisses"] = 53.52014426127423,
			["Kalano"] = 6,
			["Bakanti"] = 2.6,
			["Donaster"] = 65.97841796874999,
			["Glimmer"] = 16.525,
			["Darkshaman"] = 36.04368476867675,
			["Janarsk"] = 52.0042827545898,
			["Anarchos"] = 11.2,
			["Nipp"] = 103.4,
			["Limp"] = 103.8734375,
			["Abolish"] = 71.16988067626951,
			["Stilnox"] = 19.9,
			["Pastorcrone"] = 1.1,
			["Standawarlok"] = 178.5589128405881,
			["Diller"] = 65.02421337477864,
			["Moonies"] = 42.15624999999999,
			["Reapz"] = 101.1989096983292,
			["Skyle"] = 18,
			["Yoshimoto"] = 50.5578125,
			["Jahlight"] = 55.84861385010445,
			["Purplerat"] = 58.18249032591219,
			["Yojin"] = 6.699999999999999,
			["Standawarlock"] = 0,
			["Mythic"] = 72.82499999999999,
			["Mallfurion"] = 12.420703125,
			["Masai"] = 26.56874999999999,
			["Lookapally"] = 1,
			["Kaiiden"] = 12.9125,
			["Littlepope"] = 27.31436767578125,
			["Luciferael"] = 14.6162109375,
			["Thornak"] = 55.27390024662017,
			["Wyxan"] = 12.42806396484375,
			["S韓k"] = 45.17230918665088,
			["Nicklaswiik"] = 49.7,
			["Sixpounder"] = 112.7498674331468,
			["N靏htmare"] = 160.5467726655844,
			["Goldenwand"] = 163.5234313964844,
			["Irmishor"] = 77.47978515625003,
			["Annub韘"] = 81.70629262239996,
			["Silverstonez"] = 27.6111152901094,
			["Skep"] = 17.928125,
			["Amarilis"] = 90.50000000000003,
			["Sullen"] = 134.71,
			["Anomandaris"] = 20.9765625,
			["Modrack"] = 6,
			["Drakespotter"] = 51.27382812499999,
			["Znufflessd"] = 115.7564419515773,
			["Lysia"] = 74.2980165224523,
			["Oxider"] = 45.61875,
			["Marjory"] = 107.6768582475093,
			["Hipocrates"] = 110.91,
			["Madwarp"] = 38.8439841499554,
			["Wazzockk"] = 27.64375,
			["Casse"] = 82.34733895370744,
			["Redsnap"] = 82.81875000000002,
			["Browniee"] = 14.9,
			["Neurox"] = 142.0123014972254,
			["Undenth"] = 81.38942842581224,
			["Ghallar"] = 10,
			["Faxzorr"] = 39.02792450294366,
			["Dhaffy"] = 13.2572021484375,
			["Nealuchy"] = 24.2,
			["Kazoku"] = 120.24519861394,
			["Ozaku"] = 50.1734170750901,
			["Howll"] = 70.53942653812121,
			["Missturtle"] = 10.8,
			["Velimatti"] = 96.97339012753626,
			["Snapi"] = 4.8,
			["Zorlex"] = 83.34489687817376,
			["Barracudos"] = 8.199999999999999,
			["Twee"] = 105.8170643531485,
			["Naayse"] = 126.9,
			["Albazz"] = 51.88214008212089,
			["Rands"] = 10.8,
			["Missheals"] = 136.3382218568287,
			["Puscifer"] = 175.0551752018927,
			["H魒l"] = 40.58535041809083,
			["F醜ad"] = 2.6,
			["Lorena"] = 73.17797993007233,
			["Superfax"] = 0,
			["Samynix"] = 78.66168365867924,
			["Terab"] = 2.8,
			["Deadblack"] = 93.94579782714179,
			["D錼e"] = 11.1875,
			["Olymp"] = 28.5984375,
			["Thirnova"] = 82.84477098052523,
			["Smashing"] = 3,
			["Bahmut"] = 77.98728485107419,
			["Kiplex"] = 68.9339790189577,
			["Frankaz"] = 35.59999999999999,
			["Satyr"] = 3.715301513671875,
			["Crysanthos"] = 12.1,
			["Raziel"] = 54.59892578124997,
			["Xen"] = 47.8171875,
			["Kafo"] = 33.95000000000001,
			["Lunaatj"] = 25.2,
			["Mainrak"] = 15.74119808673859,
			["Sheve"] = 72.96606826782228,
			["Netherdruid"] = 4,
			["Jitter"] = 80.43541267343595,
			["Nerezza"] = 19.2,
			["Yumad"] = 57.10804011713954,
			["Deshai"] = 31.86718749999999,
			["Fourever"] = 3.96875,
			["Gromk鄏"] = 60.73427623669271,
			["Gomarius"] = 26.85820312499999,
			["Bubblebutt"] = 15.059375,
			["Falconcrest"] = 47.18560546875,
			["Glexy"] = 50.09467261158207,
			["Broly"] = 143.215447998047,
			["Wojtyla"] = 76.56250000000001,
			["Laloeno"] = 21,
			["Deccal"] = 56.79538574218747,
			["Littlepiggy"] = 19.8595703125,
			["Kaldrgrimmr"] = 22.53134765625,
			["Mageyoulook"] = 89.40824390664915,
			["Ains"] = 20.01286297092336,
			["Jahblin"] = 65.44852752685547,
			["Tingse"] = 6.9,
			["Harmonize"] = 57.47371152867748,
			["Wilhelm"] = 18.139013671875,
			["Clixx"] = 16.175,
			["Nuzanix"] = 20.3,
			["Ev?"] = 32.63125,
			["Deefa"] = 22.2515625,
			["Lumide"] = 25.2796875,
			["Sacrament"] = 34.46691145896911,
			["Greenrow"] = 36.815625,
			["Pureshamy"] = 11.3,
			["Tubbygold"] = 112.3197134133892,
			["Uskilla"] = 7.1,
			["Wils髇"] = 17.925,
			["Scuttlebutt"] = 64.85407714843747,
			["Spectero"] = 27.8,
			["Bingzork"] = 58.97460937499999,
			["Stj鋜tpirat"] = 50.44058861732481,
			["Holypad"] = 69.09421386718751,
			["Revex"] = 29.12885131835938,
			["Giblex"] = 61.29557364186327,
			["Sav?"] = 3.46875,
			["Xiola"] = 43.33394042968753,
			["Agonias"] = 25.9,
			["Fenteria"] = 13.6,
			["Dismantle"] = 1.1,
			["Ridikk"] = 13.475,
			["Zhopher"] = 18.1,
			["Cadaverous"] = 3,
			["Sakinio"] = 83.72360839843752,
			["Uzargah"] = 53.7,
			["Zen靦h"] = 30.63310546875001,
			["Flaytality"] = 30.4328125,
			["Asch"] = 24,
			["Youdare"] = 34.25,
			["Glexx"] = 96.89479795349136,
			["Keselamatan"] = 5.5,
			["V閘amelaxa"] = 57.95,
			["Bullsteak"] = 62.86201494510381,
			["Avaliot"] = 59.96668634414672,
			["Sensorme"] = 16,
			["Gzes"] = 86.2139735617442,
			["Lexii"] = 1.5,
			["Suppremus"] = 12.45,
			["Nihtera"] = 54.71874999999998,
			["Drekkar"] = 1.2,
			["Deathshaker"] = 16.10708417687565,
			["Isuckbigtime"] = 49.04806583523752,
			["Wilk"] = 7.5,
			["Liisanantti"] = 5.699999999999999,
			["Talkytoaster"] = 47.91855073869228,
			["Eezo"] = 7.424999999999999,
			["Naraku"] = 172.587070465088,
			["Ebica"] = 21.19234375,
			["Aceventauren"] = 5,
			["Kinigos"] = 141.325,
			["Aarwen"] = 65.27267533369734,
			["Zwitsalkid"] = 49.87586200456557,
			["Faroon"] = 28.52035051390259,
			["Soviett"] = 20.175,
			["Razhgat"] = 59.425,
			["Kohee"] = 81.23796118079324,
			["Inh"] = 21.2,
			["Vanke"] = 10.6375,
			["Koraag"] = 52.17578125000004,
			["Grekko"] = 6.65,
			["Jinkha"] = 148.6349520375164,
			["Mithrill"] = 65.09988472960455,
			["Darkblud"] = 77.07862319643684,
			["Lagwin"] = 2.9,
			["Glexor"] = 11,
			["Smoothe"] = 32.59999999999999,
			["Klesk"] = 13.8734375,
			["Standadruid"] = 5.6,
			["Este"] = 4,
			["Tirazea"] = 29.40651037693024,
			["Deadlybaker"] = 23.02175271011469,
			["Gunjah"] = 2.9,
			["Ruudolf"] = 12.825,
			["Ickis"] = 24.8315185546875,
			["Mhemnosis"] = 51.70825500488279,
			["Intro"] = 18,
			["Shevelkov"] = 18.4,
			["N雗ya"] = 3,
			["Pumpum"] = 6,
			["Deadangel"] = 3,
			["Iribal"] = 5,
			["Fuzz"] = 6,
			["Turbopippip"] = 22.58085935115814,
			["Reewez"] = 29.14369135306568,
			["Dutchegg"] = 2.6,
			["Msd"] = 1,
			["Arthuss"] = 7,
			["Fancel"] = 76,
			["Apocalyps?"] = 100.219256567955,
			["Isshin"] = 14.8,
			["Donimo"] = 28.1375,
			["Evildoc"] = 34.67125854492187,
			["Aimstaren"] = 9.725000000000001,
			["Eido"] = 27.41901125013827,
			["Augustina"] = 38.2522705078125,
			["Astraea"] = 84.77500000000003,
			["Nitalia"] = 77.15156250000001,
			["Keda"] = 47.99218749999999,
			["Bruker"] = 54.46365778744223,
			["Vate"] = 71.29377851486206,
			["Nolram"] = 6,
			["Tertius"] = 11.8,
			["Preluden"] = 28.6078125,
			["T骴"] = 6,
			["Depression"] = 24.31875,
			["Luuly"] = 26.9,
			["Iokasti"] = 5.2,
			["Parkerlewis"] = 25.2125,
			["Xsur"] = 63.28885148193271,
			["Hezekiah"] = 45.8791930607004,
			["Tho骿s"] = 43.81240234375,
			["Belie"] = 56.78018793293472,
			["Aelhia"] = 72.11211488842963,
			["Msdynamite"] = 57.34350404497852,
			["Jyscal"] = 16.875,
			["Arcadi"] = 27.9610513073206,
			["Omikron"] = 90.29614257812503,
			["Scotney"] = 23.85000000000001,
			["Feroxs"] = 2.75,
			["Kunegunda"] = 67.01597518752254,
			["Almond"] = 12,
			["Souljaxx"] = 45.09790072393639,
			["Cahira"] = 123.9350390605105,
			["Nartis"] = 68.90000000000001,
			["Islandwalker"] = 7.5,
			["Bambulance"] = 55.90195312499998,
			["Bonelady"] = 130.0804811610219,
			["Mariaeglorum"] = 80.46449127197268,
			["Reapzor"] = 100.5175882567523,
			["Heav閚ly"] = 32.48786249496042,
			["Kaeleth"] = 22.15709753036499,
			["Standacousin"] = 5.6,
			["Steeltotem"] = 20.7,
			["Keltherkain"] = 149.8924741572648,
			["Z醟"] = 14.23125000000001,
			["Lednew"] = 55.53098552393228,
			["Powerbrew"] = 30.651171875,
			["Kilionaire"] = 67.60606225119086,
			["D骳torwho"] = 86.80875795118057,
			["Plujer"] = 72.44062500000001,
			["Gobb"] = 6.84375,
			["Litigious"] = 12.6,
			["Affix"] = 119.2229248046875,
			["Ir髇jaw"] = 24.95343017578125,
			["Wendel"] = 125.4807928578717,
			["Azandai"] = 24.77099609375,
			["Xenh"] = 40.92499999999999,
			["Sipsen"] = 16.95,
			["Nruff"] = 1.5,
			["Phistashka"] = 7,
			["Miss"] = 10,
			["Zykee"] = 38.7,
			["Kotek"] = 44.21045989990233,
		}
		Test(BananaDKP)
	end

TestReferences = {}
	for i = 1, 11 do
		TestReferences["Test"..i] = function()
			TestReference("tests/reference/"..i..".txt")
		end
	end
------------------------------------------------------------------------------
for k, v in pairs(_G) do
	if type(k) == "string" and (k:find("^Test") or k:find("^test")) then
		assert(type(v) == "table", "Globals start with Test or test"
			.." must be table: "..k)
		for kk, vv in pairs(v) do
			assert(type(kk) == "string"
				and kk:find("^Test"), "All members in test table"
				.." s key must start with Test: "..tostring(kk))
			assert(type(vv) == "function", "All members in test table"
				.." must be function")
		end
	end
end

local runner = lu.LuaUnit.new()
local exitCode = runner:runSuite()
if exitCode == 0 then
	print("TEST OK")
else
	print("TEST FAILED")
end

os.exit(exitCode)