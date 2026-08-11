--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.10.9) ~  Much Love, Ferib 

]]--

local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 38) then
					if (Enum <= 18) then
						if (Enum <= 8) then
							if (Enum <= 3) then
								if (Enum <= 1) then
									if (Enum == 0) then
										local NewProto = Proto[Inst[3]];
										local NewUvals;
										local Indexes = {};
										NewUvals = Setmetatable({}, {__index=function(_, Key)
											local Val = Indexes[Key];
											return Val[1][Val[2]];
										end,__newindex=function(_, Key, Value)
											local Val = Indexes[Key];
											Val[1][Val[2]] = Value;
										end});
										for Idx = 1, Inst[4] do
											VIP = VIP + 1;
											local Mvm = Instr[VIP];
											if (Mvm[1] == 6) then
												Indexes[Idx - 1] = {Stk,Mvm[3]};
											else
												Indexes[Idx - 1] = {Upvalues,Mvm[3]};
											end
											Lupvals[#Lupvals + 1] = Indexes;
										end
										Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
									else
										local A = Inst[2];
										Stk[A](Stk[A + 1]);
									end
								elseif (Enum == 2) then
									Stk[Inst[2]] = {};
								else
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum <= 5) then
								if (Enum == 4) then
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								else
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								end
							elseif (Enum <= 6) then
								Stk[Inst[2]] = Stk[Inst[3]];
							elseif (Enum == 7) then
								do
									return;
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 13) then
							if (Enum <= 10) then
								if (Enum > 9) then
									Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
								else
									local A = Inst[2];
									local Index = Stk[A];
									local Step = Stk[A + 2];
									if (Step > 0) then
										if (Index > Stk[A + 1]) then
											VIP = Inst[3];
										else
											Stk[A + 3] = Index;
										end
									elseif (Index < Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								end
							elseif (Enum <= 11) then
								Env[Inst[3]] = Stk[Inst[2]];
							elseif (Enum > 12) then
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 15) then
							if (Enum > 14) then
								Stk[Inst[2]] = -Stk[Inst[3]];
							else
								local A = Inst[2];
								local Step = Stk[A + 2];
								local Index = Stk[A] + Step;
								Stk[A] = Index;
								if (Step > 0) then
									if (Index <= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								elseif (Index >= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							end
						elseif (Enum <= 16) then
							Stk[Inst[2]] = Env[Inst[3]];
						elseif (Enum > 17) then
							Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
						elseif Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 28) then
						if (Enum <= 23) then
							if (Enum <= 20) then
								if (Enum > 19) then
									local NewProto = Proto[Inst[3]];
									local NewUvals;
									local Indexes = {};
									NewUvals = Setmetatable({}, {__index=function(_, Key)
										local Val = Indexes[Key];
										return Val[1][Val[2]];
									end,__newindex=function(_, Key, Value)
										local Val = Indexes[Key];
										Val[1][Val[2]] = Value;
									end});
									for Idx = 1, Inst[4] do
										VIP = VIP + 1;
										local Mvm = Instr[VIP];
										if (Mvm[1] == 6) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 21) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 22) then
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum <= 25) then
							if (Enum == 24) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 26) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						elseif (Enum > 27) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						elseif (Stk[Inst[2]] < Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 33) then
						if (Enum <= 30) then
							if (Enum > 29) then
								Stk[Inst[2]] = Inst[3];
							else
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
							end
						elseif (Enum <= 31) then
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						elseif (Enum > 32) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						elseif (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 35) then
						if (Enum > 34) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						elseif (Inst[2] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 36) then
						do
							return Stk[Inst[2]];
						end
					elseif (Enum > 37) then
						local A = Inst[2];
						Stk[A](Stk[A + 1]);
					else
						Stk[Inst[2]] = -Stk[Inst[3]];
					end
				elseif (Enum <= 58) then
					if (Enum <= 48) then
						if (Enum <= 43) then
							if (Enum <= 40) then
								if (Enum == 39) then
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								end
							elseif (Enum <= 41) then
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							elseif (Enum == 42) then
								Env[Inst[3]] = Stk[Inst[2]];
							else
								Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
							end
						elseif (Enum <= 45) then
							if (Enum == 44) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							end
						elseif (Enum <= 46) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						elseif (Enum == 47) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						end
					elseif (Enum <= 53) then
						if (Enum <= 50) then
							if (Enum > 49) then
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							elseif (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 51) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						elseif (Enum == 52) then
							local A = Inst[2];
							local Step = Stk[A + 2];
							local Index = Stk[A] + Step;
							Stk[A] = Index;
							if (Step > 0) then
								if (Index <= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							elseif (Index >= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 55) then
						if (Enum > 54) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						end
					elseif (Enum <= 56) then
						if (Stk[Inst[2]] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 57) then
						local A = Inst[2];
						local Index = Stk[A];
						local Step = Stk[A + 2];
						if (Step > 0) then
							if (Index > Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						elseif (Index < Stk[A + 1]) then
							VIP = Inst[3];
						else
							Stk[A + 3] = Index;
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
					end
				elseif (Enum <= 68) then
					if (Enum <= 63) then
						if (Enum <= 60) then
							if (Enum == 59) then
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							end
						elseif (Enum <= 61) then
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						elseif (Enum == 62) then
							if (Stk[Inst[2]] < Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
						end
					elseif (Enum <= 65) then
						if (Enum > 64) then
							Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						end
					elseif (Enum <= 66) then
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					elseif (Enum == 67) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					elseif (Stk[Inst[2]] == Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 73) then
					if (Enum <= 70) then
						if (Enum == 69) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 71) then
						Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
					elseif (Enum == 72) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					else
						Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
					end
				elseif (Enum <= 75) then
					if (Enum == 74) then
						local A = Inst[2];
						local Results = {Stk[A](Stk[A + 1])};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
					end
				elseif (Enum <= 76) then
					if (Inst[2] <= Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum > 77) then
					Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
				else
					do
						return;
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!113Q0003053Q006269743332026Q002Q40027Q004003043Q00626E6F7403043Q0062616E642Q033Q00626F7203043Q0062786F7203063Q006C736869667403063Q0072736869667403073Q006172736869667403053Q007063612Q6C03043Q007479706503083Q0066756E6374696F6E03043Q007461736B03053Q00737061776E03043Q007761726E03313Q005B4C6F6164657220452Q726F725D3A204E6F207365207075646F20696E696369616C697A617220656C207363726970742E00394Q00027Q00122A3Q00013Q00121E3Q00023Q001049000100033Q001210000200013Q00061400033Q000100012Q00063Q00013Q00102E000200040003001210000200013Q00061400030001000100022Q00063Q00014Q00067Q00102E000200050003001210000200013Q00061400030002000100022Q00063Q00014Q00067Q00102E000200060003001210000200013Q00061400030003000100022Q00063Q00014Q00067Q00102E000200070003001210000200013Q00061400030004000100022Q00068Q00063Q00013Q00102E000200080003001210000200013Q00061400030005000100022Q00068Q00063Q00013Q00102E000200090003001210000200013Q00061400030006000100022Q00068Q00063Q00013Q00102E0002000A00030012100002000B3Q000230000300074Q00460002000200030006110002003500013Q0004133Q003500010012100004000C4Q0016000500034Q0028000400020002002644000400350001000D0004133Q003500010012100004000E3Q00203700040004000F2Q0016000500034Q00010004000200010004133Q00380001001210000400103Q00121E000500114Q00010004000200012Q00073Q00013Q00083Q00013Q00026Q00F03F01074Q000800016Q001F5Q00012Q000800015Q0020470001000100012Q003D000100014Q0017000100024Q00073Q00017Q000B3Q00025Q00E06F40026Q007040024Q00E0FFEF40026Q00F040022Q00E03QFFEF41026Q00F041028Q00026Q00F03F027Q004003043Q006D61746803053Q00666C2Q6F72022B3Q00264400010004000100010004133Q0004000100200A00023Q00022Q0017000200023Q00264400010008000100030004133Q0008000100200A00023Q00042Q0017000200023Q0026440001000C000100050004133Q000C000100200A00023Q00062Q0017000200024Q000800026Q001F00023Q00022Q000800036Q001F0001000100032Q00163Q00023Q00121E000200073Q00121E000300083Q00121E000400084Q0008000500013Q00121E000600083Q00043A00040029000100200A00083Q000900200A000900010009001210000A000A3Q002037000A000A000B002032000B3Q00092Q0028000A00020002001210000B000A3Q002037000B000B000B002032000C000100092Q0028000B000200022Q00160001000B4Q00163Q000A4Q0029000A00080009002644000A0027000100090004133Q002700012Q00290002000200030010410003000900030004340004001700012Q0017000200024Q00073Q00017Q000A3Q00025Q00E06F40026Q007040024Q00E0FFEF40026Q00F040022Q00E03QFFEF41028Q00026Q00F03F027Q004003043Q006D61746803053Q00666C2Q6F72022F3Q00264400010006000100010004133Q0006000100200A00023Q00022Q003D00023Q00020020390002000200012Q0017000200023Q0026440001000C000100030004133Q000C000100200A00023Q00042Q003D00023Q00020020390002000200032Q0017000200023Q00264400010010000100050004133Q0010000100121E000200054Q0017000200024Q000800026Q001F00023Q00022Q000800036Q001F0001000100032Q00163Q00023Q00121E000200063Q00121E000300073Q00121E000400074Q0008000500013Q00121E000600073Q00043A0004002D000100200A00083Q000800200A000900010008001210000A00093Q002037000A000A000A002032000B3Q00082Q0028000A00020002001210000B00093Q002037000B000B000A002032000C000100082Q0028000B000200022Q00160001000B4Q00163Q000A4Q0029000A00080009000E4C0007002B0001000A0004133Q002B00012Q00290002000200030010410003000800030004340004001B00012Q0017000200024Q00073Q00017Q00053Q00028Q00026Q00F03F027Q004003043Q006D61746803053Q00666C2Q6F72021F4Q000800026Q001F00023Q00022Q000800036Q001F0001000100032Q00163Q00023Q00121E000200013Q00121E000300023Q00121E000400024Q0008000500013Q00121E000600023Q00043A0004001D000100200A00083Q000300200A000900010003001210000A00043Q002037000A000A0005002032000B3Q00032Q0028000A00020002001210000B00043Q002037000B000B0005002032000C000100032Q0028000B000200022Q00160001000B4Q00163Q000A4Q0029000A00080009002644000A001B000100020004133Q001B00012Q00290002000200030010410003000300030004340004000B00012Q0017000200024Q00073Q00017Q00053Q0003043Q006D6174682Q033Q00616273028Q0003053Q00666C2Q6F72027Q0040021A3Q001210000200013Q0020370002000200022Q0016000300014Q00280002000200022Q000800035Q00063800030009000100020004133Q0009000100121E000200034Q0017000200024Q0008000200014Q001F5Q000200263E00010014000100030004133Q00140001001210000200013Q0020370002000200040010490003000500012Q004E00033Q00032Q0005000200034Q003300025Q0004133Q001900010010490002000500012Q004E00023Q00022Q0008000300014Q001F0002000200032Q0017000200024Q00073Q00017Q00053Q0003043Q006D6174682Q033Q00616273028Q0003053Q00666C2Q6F72027Q0040021C3Q001210000200013Q0020370002000200022Q0016000300014Q00280002000200022Q000800035Q00063800030009000100020004133Q0009000100121E000200034Q0017000200024Q0008000200014Q001F5Q0002000E0D00030015000100010004133Q00150001001210000200013Q0020370002000200042Q0025000300013Q0010490003000500032Q004E00033Q00032Q0005000200034Q003300025Q0004133Q001B00012Q0025000200013Q0010490002000500022Q004E00023Q00022Q0008000300014Q001F0002000200032Q0017000200024Q00073Q00017Q00053Q0003043Q006D6174682Q033Q00616273028Q00027Q004003053Q00666C2Q6F7202273Q001210000200013Q0020370002000200022Q0016000300014Q00280002000200022Q000800035Q00063800030009000100020004133Q0009000100121E000200034Q0017000200024Q0008000200014Q001F5Q0002000E0D00030020000100010004133Q0020000100121E000200034Q0008000300013Q0020320003000300040006380003001700013Q0004133Q001700012Q0008000300014Q000800046Q003D0004000400010010490004000400042Q003D000200030004001210000300013Q0020370003000300052Q0025000400013Q0010490004000400042Q004E00043Q00042Q00280003000200022Q00290003000300022Q0017000300023Q0004133Q002600012Q0025000200013Q0010490002000400022Q004E00023Q00022Q0008000300014Q001F0002000200032Q0017000200024Q00073Q00017Q00073Q0003043Q0067616D6503073Q00482Q747047657403783Q00682Q7470733A2Q2F6170692E6A6E6B69652E636F6D2F6170692F76312F6C7561736372697074732F7075626C69632F6538323866362Q333965303634613062653538623938636661633661306637363736303863382Q653932346561306661326362343139343964656364613265302F646F776E6C6F6164034Q0003053Q00652Q726F7203223Q00452Q726F7220616C20636F6E656374617220636F6E20656C207365727669646F722E030A3Q006C6F6164737472696E6700103Q0012103Q00013Q00201C5Q000200121E000200034Q00433Q000200020006113Q000800013Q0004133Q000800010026443Q000B000100040004133Q000B0001001210000100053Q00121E000200064Q0001000100020001001210000100074Q001600026Q0005000100024Q003300016Q00073Q00017Q00", GetFEnv(), ...);