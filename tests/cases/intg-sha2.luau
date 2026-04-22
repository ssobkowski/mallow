
--------------------------------------------------------------------------------------------------------------------------
-- sha2.lua
--------------------------------------------------------------------------------------------------------------------------
-- VERSION: 12 (2022-02-23)
-- AUTHOR:  Egor Skriptunoff
-- LICENSE: MIT (the same license as Lua itself)
-- URL:     https://github.com/Egor-Skriptunoff/pure_lua_SHA
--
-- DESCRIPTION:
--    This module contains functions to calculate SHA digest:
--       MD5, SHA-1,
--       SHA-224, SHA-256, SHA-512/224, SHA-512/256, SHA-384, SHA-512,
--       SHA3-224, SHA3-256, SHA3-384, SHA3-512, SHAKE128, SHAKE256,
--       HMAC,
--       BLAKE2b, BLAKE2s, BLAKE2bp, BLAKE2sp, BLAKE2Xb, BLAKE2Xs,
--       BLAKE3, BLAKE3_KDF
--    Written in pure Lua.
--    Compatible with:
--       Lua 5.1, Lua 5.2, Lua 5.3, Lua 5.4, Fengari, LuaJIT 2.0/2.1 (any CPU endianness).
--    Main feature of this module: it was heavily optimized for speed.
--    For every Lua version the module contains particular implementation branch to get benefits from version-specific features.
--       - branch for Lua 5.1 (emulating bitwise operators using look-up table)
--       - branch for Lua 5.2 (using bit32/bit library), suitable for both Lua 5.2 with native "bit32" and Lua 5.1 with external library "bit"
--       - branch for Lua 5.3/5.4 (using native 64-bit bitwise operators)
--       - branch for Lua 5.3/5.4 (using native 32-bit bitwise operators) for Lua built with LUA_INT_TYPE=LUA_INT_INT
--       - branch for LuaJIT without FFI library (useful in a sandboxed environment)
--       - branch for LuaJIT x86 without FFI library (LuaJIT x86 has oddity because of lack of CPU registers)
--       - branch for LuaJIT 2.0 with FFI library (bit.* functions work only with Lua numbers)
--       - branch for LuaJIT 2.1 with FFI library (bit.* functions can work with "int64_t" arguments)
--
--
-- USAGE:
--    Input data should be provided as a binary string: either as a whole string or as a sequence of substrings (chunk-by-chunk loading, total length < 9*10^15 bytes).
--    Result (SHA digest) is returned in hexadecimal representation as a string of lowercase hex digits.
--    Simplest usage example:
--       local sha = require("sha2")
--       local your_hash = sha.sha256("your string")
--    See file "sha2_test.lua" for more examples.
--
--
-- CHANGELOG:
--  version     date      description
--  -------  ----------   -----------
--    12     2022-02-23   Now works in Luau (but NOT optimized for speed)
--    11     2022-01-09   BLAKE3 added
--    10     2022-01-02   BLAKE2 functions added
--     9     2020-05-10   Now works in OpenWrt's Lua (dialect of Lua 5.1 with "double" + "invisible int32")
--     8     2019-09-03   SHA-3 functions added
--     7     2019-03-17   Added functions to convert to/from base64
--     6     2018-11-12   HMAC added
--     5     2018-11-10   SHA-1 added
--     4     2018-11-03   MD5 added
--     3     2018-11-02   Bug fixed: incorrect hashing of long (2 GByte) data streams on Lua 5.3/5.4 built with "int32" integers
--     2     2018-10-07   Decreased module loading time in Lua 5.1 implementation branch (thanks to Peter Melnichenko for giving a hint)
--     1     2018-10-06   First release (only SHA-2 functions)
-----------------------------------------------------------------------------


local print_debug_messages = false  -- set to true to view some messages about your system's abilities and implementation branch chosen for your system

local unpack, table_concat, byte, char, string_rep, sub, gsub, gmatch, string_format, floor, ceil, math_min, math_max, tonumber, type, math_huge =
   table.unpack or unpack, table.concat, string.byte, string.char, string.rep, string.sub, string.gsub, string.gmatch, string.format, math.floor, math.ceil, math.min, math.max, tonumber, type, math.huge


--------------------------------------------------------------------------------
-- EXAMINING YOUR SYSTEM
--------------------------------------------------------------------------------

local function get_precision(one)
   -- "one" must be either float 1.0 or integer 1
   -- returns bits_precision, is_integer
   -- This function works correctly with all floating point datatypes (including non-IEEE-754)
   local k, n, m, prev_n = 0, one, one
   while true do
      k, prev_n, n, m = k + 1, n, n + n + 1, m + m + k % 2
      if k > 256 or n - (n - 1) ~= 1 or m - (m - 1) ~= 1 or n == m then
         return k, false   -- floating point datatype
      elseif n == prev_n then
         return k, true    -- integer datatype
      end
   end
end

-- Make sure Lua has "double" numbers
local x = 2/3
local Lua_has_double = x * 5 > 3 and x * 4 < 3 and get_precision(1.0) >= 53
assert(Lua_has_double, "at least 53-bit floating point numbers are required")

-- Q:
--    SHA2 was designed for FPU-less machines.
--    So, why floating point numbers are needed for this module?
-- A:
--    53-bit "double" numbers are useful to calculate "magic numbers" used in SHA.
--    I prefer to write 50 LOC "magic numbers calculator" instead of storing more than 200 constants explicitly in this source file.

local int_prec, Lua_has_integers = get_precision(1)
local Lua_has_int64 = Lua_has_integers and int_prec == 64
local Lua_has_int32 = Lua_has_integers and int_prec == 32
assert(Lua_has_int64 or Lua_has_int32 or not Lua_has_integers, "Lua integers must be either 32-bit or 64-bit")

-- Q:
--    Does it mean that almost all non-standard configurations are not supported?
-- A:
--    Yes.  Sorry, too many problems to support all possible Lua numbers configurations.
--       Lua 5.1/5.2    with "int32"               will not work.
--       Lua 5.1/5.2    with "int64"               will not work.
--       Lua 5.1/5.2    with "int128"              will not work.
--       Lua 5.1/5.2    with "float"               will not work.
--       Lua 5.1/5.2    with "double"              is OK.          (default config for Lua 5.1, Lua 5.2, LuaJIT)
--       Lua 5.3/5.4    with "int32"  + "float"    will not work.
--       Lua 5.3/5.4    with "int64"  + "float"    will not work.
--       Lua 5.3/5.4    with "int128" + "float"    will not work.
--       Lua 5.3/5.4    with "int32"  + "double"   is OK.          (config used by Fengari)
--       Lua 5.3/5.4    with "int64"  + "double"   is OK.          (default config for Lua 5.3, Lua 5.4)
--       Lua 5.3/5.4    with "int128" + "double"   will not work.
--   Using floating point numbers better than "double" instead of "double" is OK (non-IEEE-754 floating point implementation are allowed).
--   Using "int128" instead of "int64" is not OK: "int128" would require different branch of implementation for optimized SHA512.

-- Check for LuaJIT and 32-bit bitwise libraries
local is_LuaJIT = ({false, [1] = true})[1] and _VERSION ~= "Luau" and (type(jit) ~= "table" or jit.version_num >= 20000)  -- LuaJIT 1.x.x and Luau are treated as vanilla Lua 5.1/5.2
local is_LuaJIT_21  -- LuaJIT 2.1+
local LuaJIT_arch
local ffi           -- LuaJIT FFI library (as a table)
local b             -- 32-bit bitwise library (as a table)
local library_name

if is_LuaJIT then
   -- Assuming "bit" library is always available on LuaJIT
   b = require"bit"
   library_name = "bit"
   -- "ffi" is intentionally disabled on some systems for safety reason
   local LuaJIT_has_FFI, result = pcall(require, "ffi")
   if LuaJIT_has_FFI then
      ffi = result
   end
   is_LuaJIT_21 = not not loadstring"b=0b0"
   LuaJIT_arch = type(jit) == "table" and jit.arch or ffi and ffi.arch or nil
else
   -- For vanilla Lua, "bit"/"bit32" libraries are searched in global namespace only.  No attempt is made to load a library if it's not loaded yet.
   for _, libname in ipairs(_VERSION == "Lua 5.2" and {"bit32", "bit"} or {"bit", "bit32"}) do
      if type(_G[libname]) == "table" and _G[libname].bxor then
         b = _G[libname]
         library_name = libname
         break
      end
   end
end

--------------------------------------------------------------------------------
-- You can disable here some of your system's abilities (for testing purposes)
--------------------------------------------------------------------------------
-- is_LuaJIT = nil
-- is_LuaJIT_21 = nil
-- ffi = nil
-- Lua_has_int32 = nil
-- Lua_has_int64 = nil
-- b, library_name = nil
--------------------------------------------------------------------------------

if print_debug_messages then
   -- Printing list of abilities of your system
   print("Abilities:")
   print("   Lua version:               "..(is_LuaJIT and "LuaJIT "..(is_LuaJIT_21 and "2.1 " or "2.0 ")..(LuaJIT_arch or "")..(ffi and " with FFI" or " without FFI") or _VERSION))
   print("   Integer bitwise operators: "..(Lua_has_int64 and "int64" or Lua_has_int32 and "int32" or "no"))
   print("   32-bit bitwise library:    "..(library_name or "not found"))
end

-- Selecting the most suitable implementation for given set of abilities
local method, branch
if is_LuaJIT and ffi then
   method = "Using 'ffi' library of LuaJIT"
   branch = "FFI"
elseif is_LuaJIT then
   method = "Using special code for sandboxed LuaJIT (no FFI)"
   branch = "LJ"
elseif Lua_has_int64 then
   method = "Using native int64 bitwise operators"
   branch = "INT64"
elseif Lua_has_int32 then
   method = "Using native int32 bitwise operators"
   branch = "INT32"
elseif library_name then   -- when bitwise library is available (Lua 5.2 with native library "bit32" or Lua 5.1 with external library "bit")
   method = "Using '"..library_name.."' library"
   branch = "LIB32"
else
   method = "Emulating bitwise operators using look-up table"
   branch = "EMUL"
end

if print_debug_messages then
   -- Printing the implementation selected to be used on your system
   print("Implementation selected:")
   print("   "..method)
end


--------------------------------------------------------------------------------
-- BASIC 32-BIT BITWISE FUNCTIONS
--------------------------------------------------------------------------------

local AND, OR, XOR, SHL, SHR, ROL, ROR, NOT, NORM, HEX, XOR_BYTE
-- Only low 32 bits of function arguments matter, high bits are ignored
-- The result of all functions (except HEX) is an integer inside "correct range":
--    for "bit" library:    (-2^31)..(2^31-1)
--    for "bit32" library:        0..(2^32-1)

if branch == "FFI" or branch == "LJ" or branch == "LIB32" then

   -- Your system has 32-bit bitwise library (either "bit" or "bit32")

   AND  = b.band                -- 2 arguments
   OR   = b.bor                 -- 2 arguments
   XOR  = b.bxor                -- 2..5 arguments
   SHL  = b.lshift              -- second argument is integer 0..31
   SHR  = b.rshift              -- second argument is integer 0..31
   ROL  = b.rol or b.lrotate    -- second argument is integer 0..31
   ROR  = b.ror or b.rrotate    -- second argument is integer 0..31
   NOT  = b.bnot                -- only for LuaJIT
   NORM = b.tobit               -- only for LuaJIT
   HEX  = b.tohex               -- returns string of 8 lowercase hexadecimal digits
   assert(AND and OR and XOR and SHL and SHR and ROL and ROR and NOT, "Library '"..library_name.."' is incomplete")
   XOR_BYTE = XOR               -- XOR of two bytes (0..255)

elseif branch == "EMUL" then

   -- Emulating 32-bit bitwise operations using 53-bit floating point arithmetic

   function SHL(x, n)
      return (x * 2^n) % 2^32
   end

   function SHR(x, n)
      x = x % 2^32 / 2^n
      return x - x % 1
   end

   function ROL(x, n)
      x = x % 2^32 * 2^n
      local r = x % 2^32
      return r + (x - r) / 2^32
   end

   function ROR(x, n)
      x = x % 2^32 / 2^n
      local r = x % 1
      return r * 2^32 + (x - r)
   end

   local AND_of_two_bytes = {[0] = 0}  -- look-up table (256*256 entries)
   local idx = 0
   for y = 0, 127 * 256, 256 do
      for x = y, y + 127 do
         x = AND_of_two_bytes[x] * 2
         AND_of_two_bytes[idx] = x
         AND_of_two_bytes[idx + 1] = x
         AND_of_two_bytes[idx + 256] = x
         AND_of_two_bytes[idx + 257] = x + 1
         idx = idx + 2
      end
      idx = idx + 256
   end

   local function and_or_xor(x, y, operation)
      -- operation: nil = AND, 1 = OR, 2 = XOR
      local x0 = x % 2^32
      local y0 = y % 2^32
      local rx = x0 % 256
      local ry = y0 % 256
      local res = AND_of_two_bytes[rx + ry * 256]
      x = x0 - rx
      y = (y0 - ry) / 256
      rx = x % 65536
      ry = y % 256
      res = res + AND_of_two_bytes[rx + ry] * 256
      x = (x - rx) / 256
      y = (y - ry) / 256
      rx = x % 65536 + y % 256
      res = res + AND_of_two_bytes[rx] * 65536
      res = res + AND_of_two_bytes[(x + y - rx) / 256] * 16777216
      if operation then
         res = x0 + y0 - operation * res
      end
      return res
   end

   function AND(x, y)
      return and_or_xor(x, y)
   end

   function OR(x, y)
      return and_or_xor(x, y, 1)
   end

   function XOR(x, y, z, t, u)          -- 2..5 arguments
      if z then
         if t then
            if u then
               t = and_or_xor(t, u, 2)
            end
            z = and_or_xor(z, t, 2)
         end
         y = and_or_xor(y, z, 2)
      end
      return and_or_xor(x, y, 2)
   end

   function XOR_BYTE(x, y)
      return x + y - 2 * AND_of_two_bytes[x + y * 256]
   end

end

HEX = HEX
   or
      pcall(string_format, "%x", 2^31) and
      function (x)  -- returns string of 8 lowercase hexadecimal digits
         return string_format("%08x", x % 4294967296)
      end
   or
      function (x)  -- for OpenWrt's dialect of Lua
         return string_format("%08x", (x + 2^31) % 2^32 - 2^31)
      end

local function XORA5(x, y)
   return XOR(x, y or 0xA5A5A5A5) % 4294967296
end

local function create_array_of_lanes()
   return {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
end


--------------------------------------------------------------------------------
-- CREATING OPTIMIZED INNER LOOP
--------------------------------------------------------------------------------

-- Inner loop functions
local sha256_feed_64, sha512_feed_128, md5_feed_64, sha1_feed_64, keccak_feed, blake2s_feed_64, blake2b_feed_128, blake3_feed_64

-- Arrays of SHA-2 "magic numbers" (in "INT64" and "FFI" branches "*_lo" arrays contain 64-bit values)
local sha2_K_lo, sha2_K_hi, sha2_H_lo, sha2_H_hi, sha3_RC_lo, sha3_RC_hi = {}, {}, {}, {}, {}, {}
local sha2_H_ext256 = {[224] = {}, [256] = sha2_H_hi}
local sha2_H_ext512_lo, sha2_H_ext512_hi = {[384] = {}, [512] = sha2_H_lo}, {[384] = {}, [512] = sha2_H_hi}
local md5_K, md5_sha1_H = {}, {0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0}
local md5_next_shift = {0, 0, 0, 0, 0, 0, 0, 0, 28, 25, 26, 27, 0, 0, 10, 9, 11, 12, 0, 15, 16, 17, 18, 0, 20, 22, 23, 21}
local HEX64, lanes_index_base  -- defined only for branches that internally use 64-bit integers: "INT64" and "FFI"
local common_W = {}    -- temporary table shared between all calculations (to avoid creating new temporary table every time)
local common_W_blake2b, common_W_blake2s, v_for_blake2s_feed_64 = common_W, common_W, {}
local K_lo_modulo, hi_factor, hi_factor_keccak = 4294967296, 0, 0
local sigma = {
   {  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15, 16 },
   { 15, 11,  5,  9, 10, 16, 14,  7,  2, 13,  1,  3, 12,  8,  6,  4 },
   { 12,  9, 13,  1,  6,  3, 16, 14, 11, 15,  4,  7,  8,  2, 10,  5 },
   {  8, 10,  4,  2, 14, 13, 12, 15,  3,  7,  6, 11,  5,  1, 16,  9 },
   { 10,  1,  6,  8,  3,  5, 11, 16, 15,  2, 12, 13,  7,  9,  4, 14 },
   {  3, 13,  7, 11,  1, 12,  9,  4,  5, 14,  8,  6, 16, 15,  2, 10 },
   { 13,  6,  2, 16, 15, 14,  5, 11,  1,  8,  7,  4, 10,  3,  9, 12 },
   { 14, 12,  8, 15, 13,  2,  4, 10,  6,  1, 16,  5,  9,  7,  3, 11 },
   {  7, 16, 15, 10, 12,  4,  1,  9, 13,  3, 14,  8,  2,  5, 11,  6 },
   { 11,  3,  9,  5,  8,  7,  2,  6, 16, 12, 10, 15,  4, 13, 14,  1 },
};  sigma[11], sigma[12] = sigma[1], sigma[2]
local perm_blake3 = {
   1, 3, 4, 11, 13, 10, 12, 6,
   1, 3, 4, 11, 13, 10,
   2, 7, 5, 8, 14, 15, 16, 9,
   2, 7, 5, 8, 14, 15,
}

local function build_keccak_format(elem)
   local keccak_format = {}
   for _, size in ipairs{1, 9, 13, 17, 18, 21} do
      keccak_format[size] = "<"..string_rep(elem, size)
   end
   return keccak_format
end


if branch == "FFI" then

   local common_W_FFI_int32 = ffi.new("int32_t[?]", 80)   -- 64 is enough for SHA256, but 80 is needed for SHA-1
   common_W_blake2s = common_W_FFI_int32
   v_for_blake2s_feed_64 = ffi.new("int32_t[?]", 16)
   perm_blake3 = ffi.new("uint8_t[?]", #perm_blake3 + 1, 0, unpack(perm_blake3))
   for j = 1, 10 do
      sigma[j] = ffi.new("uint8_t[?]", #sigma[j] + 1, 0, unpack(sigma[j]))
   end;  sigma[11], sigma[12] = sigma[1], sigma[2]


   -- SHA256 implementation for "LuaJIT with FFI" branch

   function sha256_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W, K = common_W_FFI_int32, sha2_K_hi
      for pos = offs, offs + size - 1, 64 do
         for j = 0, 15 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)   -- slow, but doesn't depend on endianness
            W[j] = OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d)
         end
         for j = 16, 63 do
            local a, b = W[j-15], W[j-2]
            W[j] = NORM( XOR(ROR(a, 7), ROL(a, 14), SHR(a, 3)) + XOR(ROL(b, 15), ROL(b, 13), SHR(b, 10)) + W[j-7] + W[j-16] )
         end
         local a, b, c, d, e, f, g, h = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
         for j = 0, 63, 8 do  -- Thanks to Peter Cawley for this workaround (unroll the loop to avoid "PHI shuffling too complex" due to PHIs overlap)
            local z = NORM( XOR(g, AND(e, XOR(f, g))) + XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + (W[j] + K[j+1] + h) )
            h, g, f, e = g, f, e, NORM( d + z )
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(g, AND(e, XOR(f, g))) + XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + (W[j+1] + K[j+2] + h) )
            h, g, f, e = g, f, e, NORM( d + z )
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(g, AND(e, XOR(f, g))) + XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + (W[j+2] + K[j+3] + h) )
            h, g, f, e = g, f, e, NORM( d + z )
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(g, AND(e, XOR(f, g))) + XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + (W[j+3] + K[j+4] + h) )
            h, g, f, e = g, f, e, NORM( d + z )
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(g, AND(e, XOR(f, g))) + XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + (W[j+4] + K[j+5] + h) )
            h, g, f, e = g, f, e, NORM( d + z )
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(g, AND(e, XOR(f, g))) + XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + (W[j+5] + K[j+6] + h) )
            h, g, f, e = g, f, e, NORM( d + z )
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(g, AND(e, XOR(f, g))) + XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + (W[j+6] + K[j+7] + h) )
            h, g, f, e = g, f, e, NORM( d + z )
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(g, AND(e, XOR(f, g))) + XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + (W[j+7] + K[j+8] + h) )
            h, g, f, e = g, f, e, NORM( d + z )
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
         end
         H[1], H[2], H[3], H[4] = NORM(a + H[1]), NORM(b + H[2]), NORM(c + H[3]), NORM(d + H[4])
         H[5], H[6], H[7], H[8] = NORM(e + H[5]), NORM(f + H[6]), NORM(g + H[7]), NORM(h + H[8])
      end
   end


   local common_W_FFI_int64 = ffi.new("int64_t[?]", 80)
   common_W_blake2b = common_W_FFI_int64
   local int64 = ffi.typeof"int64_t"
   local int32 = ffi.typeof"int32_t"
   local uint32 = ffi.typeof"uint32_t"
   hi_factor = int64(2^32)

   if is_LuaJIT_21 then   -- LuaJIT 2.1 supports bitwise 64-bit operations

      local AND64, OR64, XOR64, NOT64, SHL64, SHR64, ROL64, ROR64  -- introducing synonyms for better code readability
          = AND,   OR,   XOR,   NOT,   SHL,   SHR,   ROL,   ROR
      HEX64 = HEX


      -- BLAKE2b implementation for "LuaJIT 2.1 + FFI" branch

      do
         local v = ffi.new("int64_t[?]", 16)
         local W = common_W_blake2b

         local function G(a, b, c, d, k1, k2)
            local va, vb, vc, vd = v[a], v[b], v[c], v[d]
            va = W[k1] + (va + vb)
            vd = ROR64(XOR64(vd, va), 32)
            vc = vc + vd
            vb = ROR64(XOR64(vb, vc), 24)
            va = W[k2] + (va + vb)
            vd = ROR64(XOR64(vd, va), 16)
            vc = vc + vd
            vb = ROL64(XOR64(vb, vc), 1)
            v[a], v[b], v[c], v[d] = va, vb, vc, vd
         end

         function blake2b_feed_128(H, _, str, offs, size, bytes_compressed, last_block_size, is_last_node)
            -- offs >= 0, size >= 0, size is multiple of 128
            local h1, h2, h3, h4, h5, h6, h7, h8 = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
            for pos = offs, offs + size - 1, 128 do
               if str then
                  for j = 1, 16 do
                     pos = pos + 8
                     local a, b, c, d, e, f, g, h = byte(str, pos - 7, pos)
                     W[j] = XOR64(OR(SHL(h, 24), SHL(g, 16), SHL(f, 8), e) * int64(2^32), uint32(int32(OR(SHL(d, 24), SHL(c, 16), SHL(b, 8), a))))
                  end
               end
               v[0x0], v[0x1], v[0x2], v[0x3], v[0x4], v[0x5], v[0x6], v[0x7] = h1, h2, h3, h4, h5, h6, h7, h8
               v[0x8], v[0x9], v[0xA], v[0xB], v[0xD], v[0xE], v[0xF] = sha2_H_lo[1], sha2_H_lo[2], sha2_H_lo[3], sha2_H_lo[4], sha2_H_lo[6], sha2_H_lo[7], sha2_H_lo[8]
               bytes_compressed = bytes_compressed + (last_block_size or 128)
               v[0xC] = XOR64(sha2_H_lo[5], bytes_compressed)  -- t0 = low_8_bytes(bytes_compressed)
               -- t1 = high_8_bytes(bytes_compressed) = 0,  message length is always below 2^53 bytes
               if last_block_size then  -- flag f0
                  v[0xE] = NOT64(v[0xE])
               end
               if is_last_node then  -- flag f1
                  v[0xF] = NOT64(v[0xF])
               end
               for j = 1, 12 do
                  local row = sigma[j]
                  G(0, 4,  8, 12, row[ 1], row[ 2])
                  G(1, 5,  9, 13, row[ 3], row[ 4])
                  G(2, 6, 10, 14, row[ 5], row[ 6])
                  G(3, 7, 11, 15, row[ 7], row[ 8])
                  G(0, 5, 10, 15, row[ 9], row[10])
                  G(1, 6, 11, 12, row[11], row[12])
                  G(2, 7,  8, 13, row[13], row[14])
                  G(3, 4,  9, 14, row[15], row[16])
               end
               h1 = XOR64(h1, v[0x0], v[0x8])
               h2 = XOR64(h2, v[0x1], v[0x9])
               h3 = XOR64(h3, v[0x2], v[0xA])
               h4 = XOR64(h4, v[0x3], v[0xB])
               h5 = XOR64(h5, v[0x4], v[0xC])
               h6 = XOR64(h6, v[0x5], v[0xD])
               h7 = XOR64(h7, v[0x6], v[0xE])
               h8 = XOR64(h8, v[0x7], v[0xF])
            end
            H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8] = h1, h2, h3, h4, h5, h6, h7, h8
            return bytes_compressed
         end

      end


      -- SHA-3 implementation for "LuaJIT 2.1 + FFI" branch

      local arr64_t = ffi.typeof"int64_t[?]"
      -- lanes array is indexed from 0
      lanes_index_base = 0
      hi_factor_keccak = int64(2^32)

      function create_array_of_lanes()
         return arr64_t(30)  -- 25 + 5 for temporary usage
      end

      function keccak_feed(lanes, _, str, offs, size, block_size_in_bytes)
         -- offs >= 0, size >= 0, size is multiple of block_size_in_bytes, block_size_in_bytes is positive multiple of 8
         local RC = sha3_RC_lo
         local qwords_qty = SHR(block_size_in_bytes, 3)
         for pos = offs, offs + size - 1, block_size_in_bytes do
            for j = 0, qwords_qty - 1 do
               pos = pos + 8
               local h, g, f, e, d, c, b, a = byte(str, pos - 7, pos)   -- slow, but doesn't depend on endianness
               lanes[j] = XOR64(lanes[j], OR64(OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d) * int64(2^32), uint32(int32(OR(SHL(e, 24), SHL(f, 16), SHL(g, 8), h)))))
            end
            for round_idx = 1, 24 do
               for j = 0, 4 do
                  lanes[25 + j] = XOR64(lanes[j], lanes[j+5], lanes[j+10], lanes[j+15], lanes[j+20])
               end
               local D = XOR64(lanes[25], ROL64(lanes[27], 1))
               lanes[1], lanes[6], lanes[11], lanes[16] = ROL64(XOR64(D, lanes[6]), 44), ROL64(XOR64(D, lanes[16]), 45), ROL64(XOR64(D, lanes[1]), 1), ROL64(XOR64(D, lanes[11]), 10)
               lanes[21] = ROL64(XOR64(D, lanes[21]), 2)
               D = XOR64(lanes[26], ROL64(lanes[28], 1))
               lanes[2], lanes[7], lanes[12], lanes[22] = ROL64(XOR64(D, lanes[12]), 43), ROL64(XOR64(D, lanes[22]), 61), ROL64(XOR64(D, lanes[7]), 6), ROL64(XOR64(D, lanes[2]), 62)
               lanes[17] = ROL64(XOR64(D, lanes[17]), 15)
               D = XOR64(lanes[27], ROL64(lanes[29], 1))
               lanes[3], lanes[8], lanes[18], lanes[23] = ROL64(XOR64(D, lanes[18]), 21), ROL64(XOR64(D, lanes[3]), 28), ROL64(XOR64(D, lanes[23]), 56), ROL64(XOR64(D, lanes[8]), 55)
               lanes[13] = ROL64(XOR64(D, lanes[13]), 25)
               D = XOR64(lanes[28], ROL64(lanes[25], 1))
               lanes[4], lanes[14], lanes[19], lanes[24] = ROL64(XOR64(D, lanes[24]), 14), ROL64(XOR64(D, lanes[19]), 8), ROL64(XOR64(D, lanes[4]), 27), ROL64(XOR64(D, lanes[14]), 39)
               lanes[9] = ROL64(XOR64(D, lanes[9]), 20)
               D = XOR64(lanes[29], ROL64(lanes[26], 1))
               lanes[5], lanes[10], lanes[15], lanes[20] = ROL64(XOR64(D, lanes[10]), 3), ROL64(XOR64(D, lanes[20]), 18), ROL64(XOR64(D, lanes[5]), 36), ROL64(XOR64(D, lanes[15]), 41)
               lanes[0] = XOR64(D, lanes[0])
               lanes[0], lanes[1], lanes[2], lanes[3], lanes[4] = XOR64(lanes[0], AND64(NOT64(lanes[1]), lanes[2]), RC[round_idx]), XOR64(lanes[1], AND64(NOT64(lanes[2]), lanes[3])), XOR64(lanes[2], AND64(NOT64(lanes[3]), lanes[4])), XOR64(lanes[3], AND64(NOT64(lanes[4]), lanes[0])), XOR64(lanes[4], AND64(NOT64(lanes[0]), lanes[1]))
               lanes[5], lanes[6], lanes[7], lanes[8], lanes[9] = XOR64(lanes[8], AND64(NOT64(lanes[9]), lanes[5])), XOR64(lanes[9], AND64(NOT64(lanes[5]), lanes[6])), XOR64(lanes[5], AND64(NOT64(lanes[6]), lanes[7])), XOR64(lanes[6], AND64(NOT64(lanes[7]), lanes[8])), XOR64(lanes[7], AND64(NOT64(lanes[8]), lanes[9]))
               lanes[10], lanes[11], lanes[12], lanes[13], lanes[14] = XOR64(lanes[11], AND64(NOT64(lanes[12]), lanes[13])), XOR64(lanes[12], AND64(NOT64(lanes[13]), lanes[14])), XOR64(lanes[13], AND64(NOT64(lanes[14]), lanes[10])), XOR64(lanes[14], AND64(NOT64(lanes[10]), lanes[11])), XOR64(lanes[10], AND64(NOT64(lanes[11]), lanes[12]))
               lanes[15], lanes[16], lanes[17], lanes[18], lanes[19] = XOR64(lanes[19], AND64(NOT64(lanes[15]), lanes[16])), XOR64(lanes[15], AND64(NOT64(lanes[16]), lanes[17])), XOR64(lanes[16], AND64(NOT64(lanes[17]), lanes[18])), XOR64(lanes[17], AND64(NOT64(lanes[18]), lanes[19])), XOR64(lanes[18], AND64(NOT64(lanes[19]), lanes[15]))
               lanes[20], lanes[21], lanes[22], lanes[23], lanes[24] = XOR64(lanes[22], AND64(NOT64(lanes[23]), lanes[24])), XOR64(lanes[23], AND64(NOT64(lanes[24]), lanes[20])), XOR64(lanes[24], AND64(NOT64(lanes[20]), lanes[21])), XOR64(lanes[20], AND64(NOT64(lanes[21]), lanes[22])), XOR64(lanes[21], AND64(NOT64(lanes[22]), lanes[23]))
            end
         end
      end


      local A5_long = 0xA5A5A5A5 * int64(2^32 + 1)  -- It's impossible to use constant 0xA5A5A5A5A5A5A5A5LL because it will raise syntax error on other Lua versions

      function XORA5(long, long2)
         return XOR64(long, long2 or A5_long)
      end


      -- SHA512 implementation for "LuaJIT 2.1 + FFI" branch

      function sha512_feed_128(H, _, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 128
         local W, K = common_W_FFI_int64, sha2_K_lo
         for pos = offs, offs + size - 1, 128 do
            for j = 0, 15 do
               pos = pos + 8
               local a, b, c, d, e, f, g, h = byte(str, pos - 7, pos)   -- slow, but doesn't depend on endianness
               W[j] = OR64(OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d) * int64(2^32), uint32(int32(OR(SHL(e, 24), SHL(f, 16), SHL(g, 8), h))))
            end
            for j = 16, 79 do
               local a, b = W[j-15], W[j-2]
               W[j] = XOR64(ROR64(a, 1), ROR64(a, 8), SHR64(a, 7)) + XOR64(ROR64(b, 19), ROL64(b, 3), SHR64(b, 6)) + W[j-7] + W[j-16]
            end
            local a, b, c, d, e, f, g, h = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
            for j = 0, 79, 8 do
               local z = XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23)) + XOR64(g, AND64(e, XOR64(f, g))) + h + K[j+1] + W[j]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XOR64(AND64(XOR64(a, b), c), AND64(a, b)) + XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30)) + z
               z = XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23)) + XOR64(g, AND64(e, XOR64(f, g))) + h + K[j+2] + W[j+1]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XOR64(AND64(XOR64(a, b), c), AND64(a, b)) + XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30)) + z
               z = XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23)) + XOR64(g, AND64(e, XOR64(f, g))) + h + K[j+3] + W[j+2]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XOR64(AND64(XOR64(a, b), c), AND64(a, b)) + XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30)) + z
               z = XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23)) + XOR64(g, AND64(e, XOR64(f, g))) + h + K[j+4] + W[j+3]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XOR64(AND64(XOR64(a, b), c), AND64(a, b)) + XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30)) + z
               z = XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23)) + XOR64(g, AND64(e, XOR64(f, g))) + h + K[j+5] + W[j+4]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XOR64(AND64(XOR64(a, b), c), AND64(a, b)) + XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30)) + z
               z = XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23)) + XOR64(g, AND64(e, XOR64(f, g))) + h + K[j+6] + W[j+5]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XOR64(AND64(XOR64(a, b), c), AND64(a, b)) + XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30)) + z
               z = XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23)) + XOR64(g, AND64(e, XOR64(f, g))) + h + K[j+7] + W[j+6]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XOR64(AND64(XOR64(a, b), c), AND64(a, b)) + XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30)) + z
               z = XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23)) + XOR64(g, AND64(e, XOR64(f, g))) + h + K[j+8] + W[j+7]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XOR64(AND64(XOR64(a, b), c), AND64(a, b)) + XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30)) + z
            end
            H[1] = a + H[1]
            H[2] = b + H[2]
            H[3] = c + H[3]
            H[4] = d + H[4]
            H[5] = e + H[5]
            H[6] = f + H[6]
            H[7] = g + H[7]
            H[8] = h + H[8]
         end
      end

   else  -- LuaJIT 2.0 doesn't support 64-bit bitwise operations

      local U = ffi.new("union{int64_t i64; struct{int32_t "..(ffi.abi("le") and "lo, hi" or "hi, lo")..";} i32;}[3]")
      -- this array of unions is used for fast splitting int64 into int32_high and int32_low

      -- "xorrific" 64-bit functions :-)
      -- int64 input is splitted into two int32 parts, some bitwise 32-bit operations are performed, finally the result is converted to int64
      -- these functions are needed because bit.* functions in LuaJIT 2.0 don't work with int64_t

      local function XORROR64_1(a)
         -- return XOR64(ROR64(a, 1), ROR64(a, 8), SHR64(a, 7))
         U[0].i64 = a
         local a_lo, a_hi = U[0].i32.lo, U[0].i32.hi
         local t_lo = XOR(SHR(a_lo, 1), SHL(a_hi, 31), SHR(a_lo, 8), SHL(a_hi, 24), SHR(a_lo, 7), SHL(a_hi, 25))
         local t_hi = XOR(SHR(a_hi, 1), SHL(a_lo, 31), SHR(a_hi, 8), SHL(a_lo, 24), SHR(a_hi, 7))
         return t_hi * int64(2^32) + uint32(int32(t_lo))
      end

      local function XORROR64_2(b)
         -- return XOR64(ROR64(b, 19), ROL64(b, 3), SHR64(b, 6))
         U[0].i64 = b
         local b_lo, b_hi = U[0].i32.lo, U[0].i32.hi
         local u_lo = XOR(SHR(b_lo, 19), SHL(b_hi, 13), SHL(b_lo, 3), SHR(b_hi, 29), SHR(b_lo, 6), SHL(b_hi, 26))
         local u_hi = XOR(SHR(b_hi, 19), SHL(b_lo, 13), SHL(b_hi, 3), SHR(b_lo, 29), SHR(b_hi, 6))
         return u_hi * int64(2^32) + uint32(int32(u_lo))
      end

      local function XORROR64_3(e)
         -- return XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23))
         U[0].i64 = e
         local e_lo, e_hi = U[0].i32.lo, U[0].i32.hi
         local u_lo = XOR(SHR(e_lo, 14), SHL(e_hi, 18), SHR(e_lo, 18), SHL(e_hi, 14), SHL(e_lo, 23), SHR(e_hi, 9))
         local u_hi = XOR(SHR(e_hi, 14), SHL(e_lo, 18), SHR(e_hi, 18), SHL(e_lo, 14), SHL(e_hi, 23), SHR(e_lo, 9))
         return u_hi * int64(2^32) + uint32(int32(u_lo))
      end

      local function XORROR64_6(a)
         -- return XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30))
         U[0].i64 = a
         local b_lo, b_hi = U[0].i32.lo, U[0].i32.hi
         local u_lo = XOR(SHR(b_lo, 28), SHL(b_hi, 4), SHL(b_lo, 30), SHR(b_hi, 2), SHL(b_lo, 25), SHR(b_hi, 7))
         local u_hi = XOR(SHR(b_hi, 28), SHL(b_lo, 4), SHL(b_hi, 30), SHR(b_lo, 2), SHL(b_hi, 25), SHR(b_lo, 7))
         return u_hi * int64(2^32) + uint32(int32(u_lo))
      end

      local function XORROR64_4(e, f, g)
         -- return XOR64(g, AND64(e, XOR64(f, g)))
         U[0].i64 = f
         U[1].i64 = g
         U[2].i64 = e
         local f_lo, f_hi = U[0].i32.lo, U[0].i32.hi
         local g_lo, g_hi = U[1].i32.lo, U[1].i32.hi
         local e_lo, e_hi = U[2].i32.lo, U[2].i32.hi
         local result_lo = XOR(g_lo, AND(e_lo, XOR(f_lo, g_lo)))
         local result_hi = XOR(g_hi, AND(e_hi, XOR(f_hi, g_hi)))
         return result_hi * int64(2^32) + uint32(int32(result_lo))
      end

      local function XORROR64_5(a, b, c)
         -- return XOR64(AND64(XOR64(a, b), c), AND64(a, b))
         U[0].i64 = a
         U[1].i64 = b
         U[2].i64 = c
         local a_lo, a_hi = U[0].i32.lo, U[0].i32.hi
         local b_lo, b_hi = U[1].i32.lo, U[1].i32.hi
         local c_lo, c_hi = U[2].i32.lo, U[2].i32.hi
         local result_lo = XOR(AND(XOR(a_lo, b_lo), c_lo), AND(a_lo, b_lo))
         local result_hi = XOR(AND(XOR(a_hi, b_hi), c_hi), AND(a_hi, b_hi))
         return result_hi * int64(2^32) + uint32(int32(result_lo))
      end

      local function XORROR64_7(a, b, m)
         -- return ROR64(XOR64(a, b), m), m = 1..31
         U[0].i64 = a
         U[1].i64 = b
         local a_lo, a_hi = U[0].i32.lo, U[0].i32.hi
         local b_lo, b_hi = U[1].i32.lo, U[1].i32.hi
         local c_lo, c_hi = XOR(a_lo, b_lo), XOR(a_hi, b_hi)
         local t_lo = XOR(SHR(c_lo, m), SHL(c_hi, -m))
         local t_hi = XOR(SHR(c_hi, m), SHL(c_lo, -m))
         return t_hi * int64(2^32) + uint32(int32(t_lo))
      end

      local function XORROR64_8(a, b)
         -- return ROL64(XOR64(a, b), 1)
         U[0].i64 = a
         U[1].i64 = b
         local a_lo, a_hi = U[0].i32.lo, U[0].i32.hi
         local b_lo, b_hi = U[1].i32.lo, U[1].i32.hi
         local c_lo, c_hi = XOR(a_lo, b_lo), XOR(a_hi, b_hi)
         local t_lo = XOR(SHL(c_lo, 1), SHR(c_hi, 31))
         local t_hi = XOR(SHL(c_hi, 1), SHR(c_lo, 31))
         return t_hi * int64(2^32) + uint32(int32(t_lo))
      end

      local function XORROR64_9(a, b)
         -- return ROR64(XOR64(a, b), 32)
         U[0].i64 = a
         U[1].i64 = b
         local a_lo, a_hi = U[0].i32.lo, U[0].i32.hi
         local b_lo, b_hi = U[1].i32.lo, U[1].i32.hi
         local t_hi, t_lo = XOR(a_lo, b_lo), XOR(a_hi, b_hi)
         return t_hi * int64(2^32) + uint32(int32(t_lo))
      end

      local function XOR64(a, b)
         -- return XOR64(a, b)
         U[0].i64 = a
         U[1].i64 = b
         local a_lo, a_hi = U[0].i32.lo, U[0].i32.hi
         local b_lo, b_hi = U[1].i32.lo, U[1].i32.hi
         local t_lo, t_hi = XOR(a_lo, b_lo), XOR(a_hi, b_hi)
         return t_hi * int64(2^32) + uint32(int32(t_lo))
      end

      local function XORROR64_11(a, b, c)
         -- return XOR64(a, b, c)
         U[0].i64 = a
         U[1].i64 = b
         U[2].i64 = c
         local a_lo, a_hi = U[0].i32.lo, U[0].i32.hi
         local b_lo, b_hi = U[1].i32.lo, U[1].i32.hi
         local c_lo, c_hi = U[2].i32.lo, U[2].i32.hi
         local t_lo, t_hi = XOR(a_lo, b_lo, c_lo), XOR(a_hi, b_hi, c_hi)
         return t_hi * int64(2^32) + uint32(int32(t_lo))
      end

      function XORA5(long, long2)
         -- return XOR64(long, long2 or 0xA5A5A5A5A5A5A5A5)
         U[0].i64 = long
         local lo32, hi32 = U[0].i32.lo, U[0].i32.hi
         local long2_lo, long2_hi = 0xA5A5A5A5, 0xA5A5A5A5
         if long2 then
            U[1].i64 = long2
            long2_lo, long2_hi = U[1].i32.lo, U[1].i32.hi
         end
         lo32 = XOR(lo32, long2_lo)
         hi32 = XOR(hi32, long2_hi)
         return hi32 * int64(2^32) + uint32(int32(lo32))
      end

      function HEX64(long)
         U[0].i64 = long
         return HEX(U[0].i32.hi)..HEX(U[0].i32.lo)
      end


      -- SHA512 implementation for "LuaJIT 2.0 + FFI" branch

      function sha512_feed_128(H, _, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 128
         local W, K = common_W_FFI_int64, sha2_K_lo
         for pos = offs, offs + size - 1, 128 do
            for j = 0, 15 do
               pos = pos + 8
               local a, b, c, d, e, f, g, h = byte(str, pos - 7, pos)   -- slow, but doesn't depend on endianness
               W[j] = OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d) * int64(2^32) + uint32(int32(OR(SHL(e, 24), SHL(f, 16), SHL(g, 8), h)))
            end
            for j = 16, 79 do
               W[j] = XORROR64_1(W[j-15]) + XORROR64_2(W[j-2]) + W[j-7] + W[j-16]
            end
            local a, b, c, d, e, f, g, h = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
            for j = 0, 79, 8 do
               local z = XORROR64_3(e) + XORROR64_4(e, f, g) + h + K[j+1] + W[j]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XORROR64_5(a, b, c) + XORROR64_6(a) + z
               z = XORROR64_3(e) + XORROR64_4(e, f, g) + h + K[j+2] + W[j+1]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XORROR64_5(a, b, c) + XORROR64_6(a) + z
               z = XORROR64_3(e) + XORROR64_4(e, f, g) + h + K[j+3] + W[j+2]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XORROR64_5(a, b, c) + XORROR64_6(a) + z
               z = XORROR64_3(e) + XORROR64_4(e, f, g) + h + K[j+4] + W[j+3]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XORROR64_5(a, b, c) + XORROR64_6(a) + z
               z = XORROR64_3(e) + XORROR64_4(e, f, g) + h + K[j+5] + W[j+4]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XORROR64_5(a, b, c) + XORROR64_6(a) + z
               z = XORROR64_3(e) + XORROR64_4(e, f, g) + h + K[j+6] + W[j+5]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XORROR64_5(a, b, c) + XORROR64_6(a) + z
               z = XORROR64_3(e) + XORROR64_4(e, f, g) + h + K[j+7] + W[j+6]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XORROR64_5(a, b, c) + XORROR64_6(a) + z
               z = XORROR64_3(e) + XORROR64_4(e, f, g) + h + K[j+8] + W[j+7]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XORROR64_5(a, b, c) + XORROR64_6(a) + z
            end
            H[1] = a + H[1]
            H[2] = b + H[2]
            H[3] = c + H[3]
            H[4] = d + H[4]
            H[5] = e + H[5]
            H[6] = f + H[6]
            H[7] = g + H[7]
            H[8] = h + H[8]
         end
      end


      -- BLAKE2b implementation for "LuaJIT 2.0 + FFI" branch

      do
         local v = ffi.new("int64_t[?]", 16)
         local W = common_W_blake2b

         local function G(a, b, c, d, k1, k2)
            local va, vb, vc, vd = v[a], v[b], v[c], v[d]
            va = W[k1] + (va + vb)
            vd = XORROR64_9(vd, va)
            vc = vc + vd
            vb = XORROR64_7(vb, vc, 24)
            va = W[k2] + (va + vb)
            vd = XORROR64_7(vd, va, 16)
            vc = vc + vd
            vb = XORROR64_8(vb, vc)
            v[a], v[b], v[c], v[d] = va, vb, vc, vd
         end

         function blake2b_feed_128(H, _, str, offs, size, bytes_compressed, last_block_size, is_last_node)
            -- offs >= 0, size >= 0, size is multiple of 128
            local h1, h2, h3, h4, h5, h6, h7, h8 = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
            for pos = offs, offs + size - 1, 128 do
               if str then
                  for j = 1, 16 do
                     pos = pos + 8
                     local a, b, c, d, e, f, g, h = byte(str, pos - 7, pos)
                     W[j] = XOR64(OR(SHL(h, 24), SHL(g, 16), SHL(f, 8), e) * int64(2^32), uint32(int32(OR(SHL(d, 24), SHL(c, 16), SHL(b, 8), a))))
                  end
               end
               v[0x0], v[0x1], v[0x2], v[0x3], v[0x4], v[0x5], v[0x6], v[0x7] = h1, h2, h3, h4, h5, h6, h7, h8
               v[0x8], v[0x9], v[0xA], v[0xB], v[0xD], v[0xE], v[0xF] = sha2_H_lo[1], sha2_H_lo[2], sha2_H_lo[3], sha2_H_lo[4], sha2_H_lo[6], sha2_H_lo[7], sha2_H_lo[8]
               bytes_compressed = bytes_compressed + (last_block_size or 128)
               v[0xC] = XOR64(sha2_H_lo[5], bytes_compressed)  -- t0 = low_8_bytes(bytes_compressed)
               -- t1 = high_8_bytes(bytes_compressed) = 0,  message length is always below 2^53 bytes
               if last_block_size then  -- flag f0
                  v[0xE] = -1 - v[0xE]
               end
               if is_last_node then  -- flag f1
                  v[0xF] = -1 - v[0xF]
               end
               for j = 1, 12 do
                  local row = sigma[j]
                  G(0, 4,  8, 12, row[ 1], row[ 2])
                  G(1, 5,  9, 13, row[ 3], row[ 4])
                  G(2, 6, 10, 14, row[ 5], row[ 6])
                  G(3, 7, 11, 15, row[ 7], row[ 8])
                  G(0, 5, 10, 15, row[ 9], row[10])
                  G(1, 6, 11, 12, row[11], row[12])
                  G(2, 7,  8, 13, row[13], row[14])
                  G(3, 4,  9, 14, row[15], row[16])
               end
               h1 = XORROR64_11(h1, v[0x0], v[0x8])
               h2 = XORROR64_11(h2, v[0x1], v[0x9])
               h3 = XORROR64_11(h3, v[0x2], v[0xA])
               h4 = XORROR64_11(h4, v[0x3], v[0xB])
               h5 = XORROR64_11(h5, v[0x4], v[0xC])
               h6 = XORROR64_11(h6, v[0x5], v[0xD])
               h7 = XORROR64_11(h7, v[0x6], v[0xE])
               h8 = XORROR64_11(h8, v[0x7], v[0xF])
            end
            H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8] = h1, h2, h3, h4, h5, h6, h7, h8
            return bytes_compressed
         end

      end

   end


   -- MD5 implementation for "LuaJIT with FFI" branch

   function md5_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W, K = common_W_FFI_int32, md5_K
      for pos = offs, offs + size - 1, 64 do
         for j = 0, 15 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)   -- slow, but doesn't depend on endianness
            W[j] = OR(SHL(d, 24), SHL(c, 16), SHL(b, 8), a)
         end
         local a, b, c, d = H[1], H[2], H[3], H[4]
         for j = 0, 15, 4 do
            a, d, c, b = d, c, b, NORM(ROL(XOR(d, AND(b, XOR(c, d))) + (K[j+1] + W[j  ] + a),  7) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(d, AND(b, XOR(c, d))) + (K[j+2] + W[j+1] + a), 12) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(d, AND(b, XOR(c, d))) + (K[j+3] + W[j+2] + a), 17) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(d, AND(b, XOR(c, d))) + (K[j+4] + W[j+3] + a), 22) + b)
         end
         for j = 16, 31, 4 do
            local g = 5*j
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, AND(d, XOR(b, c))) + (K[j+1] + W[AND(g + 1, 15)] + a),  5) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, AND(d, XOR(b, c))) + (K[j+2] + W[AND(g + 6, 15)] + a),  9) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, AND(d, XOR(b, c))) + (K[j+3] + W[AND(g - 5, 15)] + a), 14) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, AND(d, XOR(b, c))) + (K[j+4] + W[AND(g    , 15)] + a), 20) + b)
         end
         for j = 32, 47, 4 do
            local g = 3*j
            a, d, c, b = d, c, b, NORM(ROL(XOR(b, c, d) + (K[j+1] + W[AND(g + 5, 15)] + a),  4) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(b, c, d) + (K[j+2] + W[AND(g + 8, 15)] + a), 11) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(b, c, d) + (K[j+3] + W[AND(g - 5, 15)] + a), 16) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(b, c, d) + (K[j+4] + W[AND(g - 2, 15)] + a), 23) + b)
         end
         for j = 48, 63, 4 do
            local g = 7*j
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, OR(b, NOT(d))) + (K[j+1] + W[AND(g    , 15)] + a),  6) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, OR(b, NOT(d))) + (K[j+2] + W[AND(g + 7, 15)] + a), 10) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, OR(b, NOT(d))) + (K[j+3] + W[AND(g - 2, 15)] + a), 15) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, OR(b, NOT(d))) + (K[j+4] + W[AND(g + 5, 15)] + a), 21) + b)
         end
         H[1], H[2], H[3], H[4] = NORM(a + H[1]), NORM(b + H[2]), NORM(c + H[3]), NORM(d + H[4])
      end
   end


   -- SHA-1 implementation for "LuaJIT with FFI" branch

   function sha1_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W = common_W_FFI_int32
      for pos = offs, offs + size - 1, 64 do
         for j = 0, 15 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)   -- slow, but doesn't depend on endianness
            W[j] = OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d)
         end
         for j = 16, 79 do
            W[j] = ROL(XOR(W[j-3], W[j-8], W[j-14], W[j-16]), 1)
         end
         local a, b, c, d, e = H[1], H[2], H[3], H[4], H[5]
         for j = 0, 19, 5 do
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j]   + 0x5A827999 + e))          -- constant = floor(2^30 * sqrt(2))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j+1] + 0x5A827999 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j+2] + 0x5A827999 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j+3] + 0x5A827999 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j+4] + 0x5A827999 + e))
         end
         for j = 20, 39, 5 do
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j]   + 0x6ED9EBA1 + e))                       -- 2^30 * sqrt(3)
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+1] + 0x6ED9EBA1 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+2] + 0x6ED9EBA1 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+3] + 0x6ED9EBA1 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+4] + 0x6ED9EBA1 + e))
         end
         for j = 40, 59, 5 do
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j]   + 0x8F1BBCDC + e))  -- 2^30 * sqrt(5)
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j+1] + 0x8F1BBCDC + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j+2] + 0x8F1BBCDC + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j+3] + 0x8F1BBCDC + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j+4] + 0x8F1BBCDC + e))
         end
         for j = 60, 79, 5 do
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j]   + 0xCA62C1D6 + e))                       -- 2^30 * sqrt(10)
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+1] + 0xCA62C1D6 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+2] + 0xCA62C1D6 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+3] + 0xCA62C1D6 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+4] + 0xCA62C1D6 + e))
         end
         H[1], H[2], H[3], H[4], H[5] = NORM(a + H[1]), NORM(b + H[2]), NORM(c + H[3]), NORM(d + H[4]), NORM(e + H[5])
      end
   end

end


if branch == "FFI" and not is_LuaJIT_21 or branch == "LJ" then

   if branch == "FFI" then
      local arr32_t = ffi.typeof"int32_t[?]"

      function create_array_of_lanes()
         return arr32_t(31)  -- 25 + 5 + 1 (due to 1-based indexing)
      end

   end


   -- SHA-3 implementation for "LuaJIT 2.0 + FFI" and "LuaJIT without FFI" branches

   function keccak_feed(lanes_lo, lanes_hi, str, offs, size, block_size_in_bytes)
      -- offs >= 0, size >= 0, size is multiple of block_size_in_bytes, block_size_in_bytes is positive multiple of 8
      local RC_lo, RC_hi = sha3_RC_lo, sha3_RC_hi
      local qwords_qty = SHR(block_size_in_bytes, 3)
      for pos = offs, offs + size - 1, block_size_in_bytes do
         for j = 1, qwords_qty do
            local a, b, c, d = byte(str, pos + 1, pos + 4)
            lanes_lo[j] = XOR(lanes_lo[j], OR(SHL(d, 24), SHL(c, 16), SHL(b, 8), a))
            pos = pos + 8
            a, b, c, d = byte(str, pos - 3, pos)
            lanes_hi[j] = XOR(lanes_hi[j], OR(SHL(d, 24), SHL(c, 16), SHL(b, 8), a))
         end
         for round_idx = 1, 24 do
            for j = 1, 5 do
               lanes_lo[25 + j] = XOR(lanes_lo[j], lanes_lo[j + 5], lanes_lo[j + 10], lanes_lo[j + 15], lanes_lo[j + 20])
            end
            for j = 1, 5 do
               lanes_hi[25 + j] = XOR(lanes_hi[j], lanes_hi[j + 5], lanes_hi[j + 10], lanes_hi[j + 15], lanes_hi[j + 20])
            end
            local D_lo = XOR(lanes_lo[26], SHL(lanes_lo[28], 1), SHR(lanes_hi[28], 31))
            local D_hi = XOR(lanes_hi[26], SHL(lanes_hi[28], 1), SHR(lanes_lo[28], 31))
            lanes_lo[2], lanes_hi[2], lanes_lo[7], lanes_hi[7], lanes_lo[12], lanes_hi[12], lanes_lo[17], lanes_hi[17] = XOR(SHR(XOR(D_lo, lanes_lo[7]), 20), SHL(XOR(D_hi, lanes_hi[7]), 12)), XOR(SHR(XOR(D_hi, lanes_hi[7]), 20), SHL(XOR(D_lo, lanes_lo[7]), 12)), XOR(SHR(XOR(D_lo, lanes_lo[17]), 19), SHL(XOR(D_hi, lanes_hi[17]), 13)), XOR(SHR(XOR(D_hi, lanes_hi[17]), 19), SHL(XOR(D_lo, lanes_lo[17]), 13)), XOR(SHL(XOR(D_lo, lanes_lo[2]), 1), SHR(XOR(D_hi, lanes_hi[2]), 31)), XOR(SHL(XOR(D_hi, lanes_hi[2]), 1), SHR(XOR(D_lo, lanes_lo[2]), 31)), XOR(SHL(XOR(D_lo, lanes_lo[12]), 10), SHR(XOR(D_hi, lanes_hi[12]), 22)), XOR(SHL(XOR(D_hi, lanes_hi[12]), 10), SHR(XOR(D_lo, lanes_lo[12]), 22))
            local L, H = XOR(D_lo, lanes_lo[22]), XOR(D_hi, lanes_hi[22])
            lanes_lo[22], lanes_hi[22] = XOR(SHL(L, 2), SHR(H, 30)), XOR(SHL(H, 2), SHR(L, 30))
            D_lo = XOR(lanes_lo[27], SHL(lanes_lo[29], 1), SHR(lanes_hi[29], 31))
            D_hi = XOR(lanes_hi[27], SHL(lanes_hi[29], 1), SHR(lanes_lo[29], 31))
            lanes_lo[3], lanes_hi[3], lanes_lo[8], lanes_hi[8], lanes_lo[13], lanes_hi[13], lanes_lo[23], lanes_hi[23] = XOR(SHR(XOR(D_lo, lanes_lo[13]), 21), SHL(XOR(D_hi, lanes_hi[13]), 11)), XOR(SHR(XOR(D_hi, lanes_hi[13]), 21), SHL(XOR(D_lo, lanes_lo[13]), 11)), XOR(SHR(XOR(D_lo, lanes_lo[23]), 3), SHL(XOR(D_hi, lanes_hi[23]), 29)), XOR(SHR(XOR(D_hi, lanes_hi[23]), 3), SHL(XOR(D_lo, lanes_lo[23]), 29)), XOR(SHL(XOR(D_lo, lanes_lo[8]), 6), SHR(XOR(D_hi, lanes_hi[8]), 26)), XOR(SHL(XOR(D_hi, lanes_hi[8]), 6), SHR(XOR(D_lo, lanes_lo[8]), 26)), XOR(SHR(XOR(D_lo, lanes_lo[3]), 2), SHL(XOR(D_hi, lanes_hi[3]), 30)), XOR(SHR(XOR(D_hi, lanes_hi[3]), 2), SHL(XOR(D_lo, lanes_lo[3]), 30))
            L, H = XOR(D_lo, lanes_lo[18]), XOR(D_hi, lanes_hi[18])
            lanes_lo[18], lanes_hi[18] = XOR(SHL(L, 15), SHR(H, 17)), XOR(SHL(H, 15), SHR(L, 17))
            D_lo = XOR(lanes_lo[28], SHL(lanes_lo[30], 1), SHR(lanes_hi[30], 31))
            D_hi = XOR(lanes_hi[28], SHL(lanes_hi[30], 1), SHR(lanes_lo[30], 31))
            lanes_lo[4], lanes_hi[4], lanes_lo[9], lanes_hi[9], lanes_lo[19], lanes_hi[19], lanes_lo[24], lanes_hi[24] = XOR(SHL(XOR(D_lo, lanes_lo[19]), 21), SHR(XOR(D_hi, lanes_hi[19]), 11)), XOR(SHL(XOR(D_hi, lanes_hi[19]), 21), SHR(XOR(D_lo, lanes_lo[19]), 11)), XOR(SHL(XOR(D_lo, lanes_lo[4]), 28), SHR(XOR(D_hi, lanes_hi[4]), 4)), XOR(SHL(XOR(D_hi, lanes_hi[4]), 28), SHR(XOR(D_lo, lanes_lo[4]), 4)), XOR(SHR(XOR(D_lo, lanes_lo[24]), 8), SHL(XOR(D_hi, lanes_hi[24]), 24)), XOR(SHR(XOR(D_hi, lanes_hi[24]), 8), SHL(XOR(D_lo, lanes_lo[24]), 24)), XOR(SHR(XOR(D_lo, lanes_lo[9]), 9), SHL(XOR(D_hi, lanes_hi[9]), 23)), XOR(SHR(XOR(D_hi, lanes_hi[9]), 9), SHL(XOR(D_lo, lanes_lo[9]), 23))
            L, H = XOR(D_lo, lanes_lo[14]), XOR(D_hi, lanes_hi[14])
            lanes_lo[14], lanes_hi[14] = XOR(SHL(L, 25), SHR(H, 7)), XOR(SHL(H, 25), SHR(L, 7))
            D_lo = XOR(lanes_lo[29], SHL(lanes_lo[26], 1), SHR(lanes_hi[26], 31))
            D_hi = XOR(lanes_hi[29], SHL(lanes_hi[26], 1), SHR(lanes_lo[26], 31))
            lanes_lo[5], lanes_hi[5], lanes_lo[15], lanes_hi[15], lanes_lo[20], lanes_hi[20], lanes_lo[25], lanes_hi[25] = XOR(SHL(XOR(D_lo, lanes_lo[25]), 14), SHR(XOR(D_hi, lanes_hi[25]), 18)), XOR(SHL(XOR(D_hi, lanes_hi[25]), 14), SHR(XOR(D_lo, lanes_lo[25]), 18)), XOR(SHL(XOR(D_lo, lanes_lo[20]), 8), SHR(XOR(D_hi, lanes_hi[20]), 24)), XOR(SHL(XOR(D_hi, lanes_hi[20]), 8), SHR(XOR(D_lo, lanes_lo[20]), 24)), XOR(SHL(XOR(D_lo, lanes_lo[5]), 27), SHR(XOR(D_hi, lanes_hi[5]), 5)), XOR(SHL(XOR(D_hi, lanes_hi[5]), 27), SHR(XOR(D_lo, lanes_lo[5]), 5)), XOR(SHR(XOR(D_lo, lanes_lo[15]), 25), SHL(XOR(D_hi, lanes_hi[15]), 7)), XOR(SHR(XOR(D_hi, lanes_hi[15]), 25), SHL(XOR(D_lo, lanes_lo[15]), 7))
            L, H = XOR(D_lo, lanes_lo[10]), XOR(D_hi, lanes_hi[10])
            lanes_lo[10], lanes_hi[10] = XOR(SHL(L, 20), SHR(H, 12)), XOR(SHL(H, 20), SHR(L, 12))
            D_lo = XOR(lanes_lo[30], SHL(lanes_lo[27], 1), SHR(lanes_hi[27], 31))
            D_hi = XOR(lanes_hi[30], SHL(lanes_hi[27], 1), SHR(lanes_lo[27], 31))
            lanes_lo[6], lanes_hi[6], lanes_lo[11], lanes_hi[11], lanes_lo[16], lanes_hi[16], lanes_lo[21], lanes_hi[21] = XOR(SHL(XOR(D_lo, lanes_lo[11]), 3), SHR(XOR(D_hi, lanes_hi[11]), 29)), XOR(SHL(XOR(D_hi, lanes_hi[11]), 3), SHR(XOR(D_lo, lanes_lo[11]), 29)), XOR(SHL(XOR(D_lo, lanes_lo[21]), 18), SHR(XOR(D_hi, lanes_hi[21]), 14)), XOR(SHL(XOR(D_hi, lanes_hi[21]), 18), SHR(XOR(D_lo, lanes_lo[21]), 14)), XOR(SHR(XOR(D_lo, lanes_lo[6]), 28), SHL(XOR(D_hi, lanes_hi[6]), 4)), XOR(SHR(XOR(D_hi, lanes_hi[6]), 28), SHL(XOR(D_lo, lanes_lo[6]), 4)), XOR(SHR(XOR(D_lo, lanes_lo[16]), 23), SHL(XOR(D_hi, lanes_hi[16]), 9)), XOR(SHR(XOR(D_hi, lanes_hi[16]), 23), SHL(XOR(D_lo, lanes_lo[16]), 9))
            lanes_lo[1], lanes_hi[1] = XOR(D_lo, lanes_lo[1]), XOR(D_hi, lanes_hi[1])
            lanes_lo[1], lanes_lo[2], lanes_lo[3], lanes_lo[4], lanes_lo[5] = XOR(lanes_lo[1], AND(NOT(lanes_lo[2]), lanes_lo[3]), RC_lo[round_idx]), XOR(lanes_lo[2], AND(NOT(lanes_lo[3]), lanes_lo[4])), XOR(lanes_lo[3], AND(NOT(lanes_lo[4]), lanes_lo[5])), XOR(lanes_lo[4], AND(NOT(lanes_lo[5]), lanes_lo[1])), XOR(lanes_lo[5], AND(NOT(lanes_lo[1]), lanes_lo[2]))
            lanes_lo[6], lanes_lo[7], lanes_lo[8], lanes_lo[9], lanes_lo[10] = XOR(lanes_lo[9], AND(NOT(lanes_lo[10]), lanes_lo[6])), XOR(lanes_lo[10], AND(NOT(lanes_lo[6]), lanes_lo[7])), XOR(lanes_lo[6], AND(NOT(lanes_lo[7]), lanes_lo[8])), XOR(lanes_lo[7], AND(NOT(lanes_lo[8]), lanes_lo[9])), XOR(lanes_lo[8], AND(NOT(lanes_lo[9]), lanes_lo[10]))
            lanes_lo[11], lanes_lo[12], lanes_lo[13], lanes_lo[14], lanes_lo[15] = XOR(lanes_lo[12], AND(NOT(lanes_lo[13]), lanes_lo[14])), XOR(lanes_lo[13], AND(NOT(lanes_lo[14]), lanes_lo[15])), XOR(lanes_lo[14], AND(NOT(lanes_lo[15]), lanes_lo[11])), XOR(lanes_lo[15], AND(NOT(lanes_lo[11]), lanes_lo[12])), XOR(lanes_lo[11], AND(NOT(lanes_lo[12]), lanes_lo[13]))
            lanes_lo[16], lanes_lo[17], lanes_lo[18], lanes_lo[19], lanes_lo[20] = XOR(lanes_lo[20], AND(NOT(lanes_lo[16]), lanes_lo[17])), XOR(lanes_lo[16], AND(NOT(lanes_lo[17]), lanes_lo[18])), XOR(lanes_lo[17], AND(NOT(lanes_lo[18]), lanes_lo[19])), XOR(lanes_lo[18], AND(NOT(lanes_lo[19]), lanes_lo[20])), XOR(lanes_lo[19], AND(NOT(lanes_lo[20]), lanes_lo[16]))
            lanes_lo[21], lanes_lo[22], lanes_lo[23], lanes_lo[24], lanes_lo[25] = XOR(lanes_lo[23], AND(NOT(lanes_lo[24]), lanes_lo[25])), XOR(lanes_lo[24], AND(NOT(lanes_lo[25]), lanes_lo[21])), XOR(lanes_lo[25], AND(NOT(lanes_lo[21]), lanes_lo[22])), XOR(lanes_lo[21], AND(NOT(lanes_lo[22]), lanes_lo[23])), XOR(lanes_lo[22], AND(NOT(lanes_lo[23]), lanes_lo[24]))
            lanes_hi[1], lanes_hi[2], lanes_hi[3], lanes_hi[4], lanes_hi[5] = XOR(lanes_hi[1], AND(NOT(lanes_hi[2]), lanes_hi[3]), RC_hi[round_idx]), XOR(lanes_hi[2], AND(NOT(lanes_hi[3]), lanes_hi[4])), XOR(lanes_hi[3], AND(NOT(lanes_hi[4]), lanes_hi[5])), XOR(lanes_hi[4], AND(NOT(lanes_hi[5]), lanes_hi[1])), XOR(lanes_hi[5], AND(NOT(lanes_hi[1]), lanes_hi[2]))
            lanes_hi[6], lanes_hi[7], lanes_hi[8], lanes_hi[9], lanes_hi[10] = XOR(lanes_hi[9], AND(NOT(lanes_hi[10]), lanes_hi[6])), XOR(lanes_hi[10], AND(NOT(lanes_hi[6]), lanes_hi[7])), XOR(lanes_hi[6], AND(NOT(lanes_hi[7]), lanes_hi[8])), XOR(lanes_hi[7], AND(NOT(lanes_hi[8]), lanes_hi[9])), XOR(lanes_hi[8], AND(NOT(lanes_hi[9]), lanes_hi[10]))
            lanes_hi[11], lanes_hi[12], lanes_hi[13], lanes_hi[14], lanes_hi[15] = XOR(lanes_hi[12], AND(NOT(lanes_hi[13]), lanes_hi[14])), XOR(lanes_hi[13], AND(NOT(lanes_hi[14]), lanes_hi[15])), XOR(lanes_hi[14], AND(NOT(lanes_hi[15]), lanes_hi[11])), XOR(lanes_hi[15], AND(NOT(lanes_hi[11]), lanes_hi[12])), XOR(lanes_hi[11], AND(NOT(lanes_hi[12]), lanes_hi[13]))
            lanes_hi[16], lanes_hi[17], lanes_hi[18], lanes_hi[19], lanes_hi[20] = XOR(lanes_hi[20], AND(NOT(lanes_hi[16]), lanes_hi[17])), XOR(lanes_hi[16], AND(NOT(lanes_hi[17]), lanes_hi[18])), XOR(lanes_hi[17], AND(NOT(lanes_hi[18]), lanes_hi[19])), XOR(lanes_hi[18], AND(NOT(lanes_hi[19]), lanes_hi[20])), XOR(lanes_hi[19], AND(NOT(lanes_hi[20]), lanes_hi[16]))
            lanes_hi[21], lanes_hi[22], lanes_hi[23], lanes_hi[24], lanes_hi[25] = XOR(lanes_hi[23], AND(NOT(lanes_hi[24]), lanes_hi[25])), XOR(lanes_hi[24], AND(NOT(lanes_hi[25]), lanes_hi[21])), XOR(lanes_hi[25], AND(NOT(lanes_hi[21]), lanes_hi[22])), XOR(lanes_hi[21], AND(NOT(lanes_hi[22]), lanes_hi[23])), XOR(lanes_hi[22], AND(NOT(lanes_hi[23]), lanes_hi[24]))
         end
      end
   end

end


if branch == "LJ" then


   -- SHA256 implementation for "LuaJIT without FFI" branch

   function sha256_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W, K = common_W, sha2_K_hi
      for pos = offs, offs + size - 1, 64 do
         for j = 1, 16 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)
            W[j] = OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d)
         end
         for j = 17, 64 do
            local a, b = W[j-15], W[j-2]
            W[j] = NORM( NORM( XOR(ROR(a, 7), ROL(a, 14), SHR(a, 3)) + XOR(ROL(b, 15), ROL(b, 13), SHR(b, 10)) ) + NORM( W[j-7] + W[j-16] ) )
         end
         local a, b, c, d, e, f, g, h = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
         for j = 1, 64, 8 do  -- Thanks to Peter Cawley for this workaround (unroll the loop to avoid "PHI shuffling too complex" due to PHIs overlap)
            local z = NORM( XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + XOR(g, AND(e, XOR(f, g))) + (K[j] + W[j] + h) )
            h, g, f, e = g, f, e, NORM(d + z)
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + XOR(g, AND(e, XOR(f, g))) + (K[j+1] + W[j+1] + h) )
            h, g, f, e = g, f, e, NORM(d + z)
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + XOR(g, AND(e, XOR(f, g))) + (K[j+2] + W[j+2] + h) )
            h, g, f, e = g, f, e, NORM(d + z)
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + XOR(g, AND(e, XOR(f, g))) + (K[j+3] + W[j+3] + h) )
            h, g, f, e = g, f, e, NORM(d + z)
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + XOR(g, AND(e, XOR(f, g))) + (K[j+4] + W[j+4] + h) )
            h, g, f, e = g, f, e, NORM(d + z)
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + XOR(g, AND(e, XOR(f, g))) + (K[j+5] + W[j+5] + h) )
            h, g, f, e = g, f, e, NORM(d + z)
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + XOR(g, AND(e, XOR(f, g))) + (K[j+6] + W[j+6] + h) )
            h, g, f, e = g, f, e, NORM(d + z)
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + XOR(g, AND(e, XOR(f, g))) + (K[j+7] + W[j+7] + h) )
            h, g, f, e = g, f, e, NORM(d + z)
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
         end
         H[1], H[2], H[3], H[4] = NORM(a + H[1]), NORM(b + H[2]), NORM(c + H[3]), NORM(d + H[4])
         H[5], H[6], H[7], H[8] = NORM(e + H[5]), NORM(f + H[6]), NORM(g + H[7]), NORM(h + H[8])
      end
   end

   local function ADD64_4(a_lo, a_hi, b_lo, b_hi, c_lo, c_hi, d_lo, d_hi)
      local sum_lo = a_lo % 2^32 + b_lo % 2^32 + c_lo % 2^32 + d_lo % 2^32
      local sum_hi = a_hi + b_hi + c_hi + d_hi
      local result_lo = NORM( sum_lo )
      local result_hi = NORM( sum_hi + floor(sum_lo / 2^32) )
      return result_lo, result_hi
   end

   if LuaJIT_arch == "x86" then  -- Special trick is required to avoid "PHI shuffling too complex" on x86 platform


      -- SHA512 implementation for "LuaJIT x86 without FFI" branch

      function sha512_feed_128(H_lo, H_hi, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 128
         -- W1_hi, W1_lo, W2_hi, W2_lo, ...   Wk_hi = W[2*k-1], Wk_lo = W[2*k]
         local W, K_lo, K_hi = common_W, sha2_K_lo, sha2_K_hi
         for pos = offs, offs + size - 1, 128 do
            for j = 1, 16*2 do
               pos = pos + 4
               local a, b, c, d = byte(str, pos - 3, pos)
               W[j] = OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d)
            end
            for jj = 17*2, 80*2, 2 do
               local a_lo, a_hi = W[jj-30], W[jj-31]
               local t_lo = XOR(OR(SHR(a_lo, 1), SHL(a_hi, 31)), OR(SHR(a_lo, 8), SHL(a_hi, 24)), OR(SHR(a_lo, 7), SHL(a_hi, 25)))
               local t_hi = XOR(OR(SHR(a_hi, 1), SHL(a_lo, 31)), OR(SHR(a_hi, 8), SHL(a_lo, 24)), SHR(a_hi, 7))
               local b_lo, b_hi = W[jj-4], W[jj-5]
               local u_lo = XOR(OR(SHR(b_lo, 19), SHL(b_hi, 13)), OR(SHL(b_lo, 3), SHR(b_hi, 29)), OR(SHR(b_lo, 6), SHL(b_hi, 26)))
               local u_hi = XOR(OR(SHR(b_hi, 19), SHL(b_lo, 13)), OR(SHL(b_hi, 3), SHR(b_lo, 29)), SHR(b_hi, 6))
               W[jj], W[jj-1] = ADD64_4(t_lo, t_hi, u_lo, u_hi, W[jj-14], W[jj-15], W[jj-32], W[jj-33])
            end
            local a_lo, b_lo, c_lo, d_lo, e_lo, f_lo, g_lo, h_lo = H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8]
            local a_hi, b_hi, c_hi, d_hi, e_hi, f_hi, g_hi, h_hi = H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8]
            local zero = 0
            for j = 1, 80 do
               local t_lo = XOR(g_lo, AND(e_lo, XOR(f_lo, g_lo)))
               local t_hi = XOR(g_hi, AND(e_hi, XOR(f_hi, g_hi)))
               local u_lo = XOR(OR(SHR(e_lo, 14), SHL(e_hi, 18)), OR(SHR(e_lo, 18), SHL(e_hi, 14)), OR(SHL(e_lo, 23), SHR(e_hi, 9)))
               local u_hi = XOR(OR(SHR(e_hi, 14), SHL(e_lo, 18)), OR(SHR(e_hi, 18), SHL(e_lo, 14)), OR(SHL(e_hi, 23), SHR(e_lo, 9)))
               local sum_lo = u_lo % 2^32 + t_lo % 2^32 + h_lo % 2^32 + K_lo[j] + W[2*j] % 2^32
               local z_lo, z_hi = NORM( sum_lo ), NORM( u_hi + t_hi + h_hi + K_hi[j] + W[2*j-1] + floor(sum_lo / 2^32) )
               zero = zero + zero  -- this thick is needed to avoid "PHI shuffling too complex" due to PHIs overlap
               h_lo, h_hi, g_lo, g_hi, f_lo, f_hi = OR(zero, g_lo), OR(zero, g_hi), OR(zero, f_lo), OR(zero, f_hi), OR(zero, e_lo), OR(zero, e_hi)
               local sum_lo = z_lo % 2^32 + d_lo % 2^32
               e_lo, e_hi = NORM( sum_lo ), NORM( z_hi + d_hi + floor(sum_lo / 2^32) )
               d_lo, d_hi, c_lo, c_hi, b_lo, b_hi = OR(zero, c_lo), OR(zero, c_hi), OR(zero, b_lo), OR(zero, b_hi), OR(zero, a_lo), OR(zero, a_hi)
               u_lo = XOR(OR(SHR(b_lo, 28), SHL(b_hi, 4)), OR(SHL(b_lo, 30), SHR(b_hi, 2)), OR(SHL(b_lo, 25), SHR(b_hi, 7)))
               u_hi = XOR(OR(SHR(b_hi, 28), SHL(b_lo, 4)), OR(SHL(b_hi, 30), SHR(b_lo, 2)), OR(SHL(b_hi, 25), SHR(b_lo, 7)))
               t_lo = OR(AND(d_lo, c_lo), AND(b_lo, XOR(d_lo, c_lo)))
               t_hi = OR(AND(d_hi, c_hi), AND(b_hi, XOR(d_hi, c_hi)))
               local sum_lo = z_lo % 2^32 + t_lo % 2^32 + u_lo % 2^32
               a_lo, a_hi = NORM( sum_lo ), NORM( z_hi + t_hi + u_hi + floor(sum_lo / 2^32) )
            end
            H_lo[1], H_hi[1] = ADD64_4(H_lo[1], H_hi[1], a_lo, a_hi, 0, 0, 0, 0)
            H_lo[2], H_hi[2] = ADD64_4(H_lo[2], H_hi[2], b_lo, b_hi, 0, 0, 0, 0)
            H_lo[3], H_hi[3] = ADD64_4(H_lo[3], H_hi[3], c_lo, c_hi, 0, 0, 0, 0)
            H_lo[4], H_hi[4] = ADD64_4(H_lo[4], H_hi[4], d_lo, d_hi, 0, 0, 0, 0)
            H_lo[5], H_hi[5] = ADD64_4(H_lo[5], H_hi[5], e_lo, e_hi, 0, 0, 0, 0)
            H_lo[6], H_hi[6] = ADD64_4(H_lo[6], H_hi[6], f_lo, f_hi, 0, 0, 0, 0)
            H_lo[7], H_hi[7] = ADD64_4(H_lo[7], H_hi[7], g_lo, g_hi, 0, 0, 0, 0)
            H_lo[8], H_hi[8] = ADD64_4(H_lo[8], H_hi[8], h_lo, h_hi, 0, 0, 0, 0)
         end
      end

   else  -- all platforms except x86


      -- SHA512 implementation for "LuaJIT non-x86 without FFI" branch

      function sha512_feed_128(H_lo, H_hi, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 128
         -- W1_hi, W1_lo, W2_hi, W2_lo, ...   Wk_hi = W[2*k-1], Wk_lo = W[2*k]
         local W, K_lo, K_hi = common_W, sha2_K_lo, sha2_K_hi
         for pos = offs, offs + size - 1, 128 do
            for j = 1, 16*2 do
               pos = pos + 4
               local a, b, c, d = byte(str, pos - 3, pos)
               W[j] = OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d)
            end
            for jj = 17*2, 80*2, 2 do
               local a_lo, a_hi = W[jj-30], W[jj-31]
               local t_lo = XOR(OR(SHR(a_lo, 1), SHL(a_hi, 31)), OR(SHR(a_lo, 8), SHL(a_hi, 24)), OR(SHR(a_lo, 7), SHL(a_hi, 25)))
               local t_hi = XOR(OR(SHR(a_hi, 1), SHL(a_lo, 31)), OR(SHR(a_hi, 8), SHL(a_lo, 24)), SHR(a_hi, 7))
               local b_lo, b_hi = W[jj-4], W[jj-5]
               local u_lo = XOR(OR(SHR(b_lo, 19), SHL(b_hi, 13)), OR(SHL(b_lo, 3), SHR(b_hi, 29)), OR(SHR(b_lo, 6), SHL(b_hi, 26)))
               local u_hi = XOR(OR(SHR(b_hi, 19), SHL(b_lo, 13)), OR(SHL(b_hi, 3), SHR(b_lo, 29)), SHR(b_hi, 6))
               W[jj], W[jj-1] = ADD64_4(t_lo, t_hi, u_lo, u_hi, W[jj-14], W[jj-15], W[jj-32], W[jj-33])
            end
            local a_lo, b_lo, c_lo, d_lo, e_lo, f_lo, g_lo, h_lo = H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8]
            local a_hi, b_hi, c_hi, d_hi, e_hi, f_hi, g_hi, h_hi = H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8]
            for j = 1, 80 do
               local t_lo = XOR(g_lo, AND(e_lo, XOR(f_lo, g_lo)))
               local t_hi = XOR(g_hi, AND(e_hi, XOR(f_hi, g_hi)))
               local u_lo = XOR(OR(SHR(e_lo, 14), SHL(e_hi, 18)), OR(SHR(e_lo, 18), SHL(e_hi, 14)), OR(SHL(e_lo, 23), SHR(e_hi, 9)))
               local u_hi = XOR(OR(SHR(e_hi, 14), SHL(e_lo, 18)), OR(SHR(e_hi, 18), SHL(e_lo, 14)), OR(SHL(e_hi, 23), SHR(e_lo, 9)))
               local sum_lo = u_lo % 2^32 + t_lo % 2^32 + h_lo % 2^32 + K_lo[j] + W[2*j] % 2^32
               local z_lo, z_hi = NORM( sum_lo ), NORM( u_hi + t_hi + h_hi + K_hi[j] + W[2*j-1] + floor(sum_lo / 2^32) )
               h_lo, h_hi, g_lo, g_hi, f_lo, f_hi = g_lo, g_hi, f_lo, f_hi, e_lo, e_hi
               local sum_lo = z_lo % 2^32 + d_lo % 2^32
               e_lo, e_hi = NORM( sum_lo ), NORM( z_hi + d_hi + floor(sum_lo / 2^32) )
               d_lo, d_hi, c_lo, c_hi, b_lo, b_hi = c_lo, c_hi, b_lo, b_hi, a_lo, a_hi
               u_lo = XOR(OR(SHR(b_lo, 28), SHL(b_hi, 4)), OR(SHL(b_lo, 30), SHR(b_hi, 2)), OR(SHL(b_lo, 25), SHR(b_hi, 7)))
               u_hi = XOR(OR(SHR(b_hi, 28), SHL(b_lo, 4)), OR(SHL(b_hi, 30), SHR(b_lo, 2)), OR(SHL(b_hi, 25), SHR(b_lo, 7)))
               t_lo = OR(AND(d_lo, c_lo), AND(b_lo, XOR(d_lo, c_lo)))
               t_hi = OR(AND(d_hi, c_hi), AND(b_hi, XOR(d_hi, c_hi)))
               local sum_lo = z_lo % 2^32 + u_lo % 2^32 + t_lo % 2^32
               a_lo, a_hi = NORM( sum_lo ), NORM( z_hi + u_hi + t_hi + floor(sum_lo / 2^32) )
            end
            H_lo[1], H_hi[1] = ADD64_4(H_lo[1], H_hi[1], a_lo, a_hi, 0, 0, 0, 0)
            H_lo[2], H_hi[2] = ADD64_4(H_lo[2], H_hi[2], b_lo, b_hi, 0, 0, 0, 0)
            H_lo[3], H_hi[3] = ADD64_4(H_lo[3], H_hi[3], c_lo, c_hi, 0, 0, 0, 0)
            H_lo[4], H_hi[4] = ADD64_4(H_lo[4], H_hi[4], d_lo, d_hi, 0, 0, 0, 0)
            H_lo[5], H_hi[5] = ADD64_4(H_lo[5], H_hi[5], e_lo, e_hi, 0, 0, 0, 0)
            H_lo[6], H_hi[6] = ADD64_4(H_lo[6], H_hi[6], f_lo, f_hi, 0, 0, 0, 0)
            H_lo[7], H_hi[7] = ADD64_4(H_lo[7], H_hi[7], g_lo, g_hi, 0, 0, 0, 0)
            H_lo[8], H_hi[8] = ADD64_4(H_lo[8], H_hi[8], h_lo, h_hi, 0, 0, 0, 0)
         end
      end

   end


   -- MD5 implementation for "LuaJIT without FFI" branch

   function md5_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W, K = common_W, md5_K
      for pos = offs, offs + size - 1, 64 do
         for j = 1, 16 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)
            W[j] = OR(SHL(d, 24), SHL(c, 16), SHL(b, 8), a)
         end
         local a, b, c, d = H[1], H[2], H[3], H[4]
         for j = 1, 16, 4 do
            a, d, c, b = d, c, b, NORM(ROL(XOR(d, AND(b, XOR(c, d))) + (K[j  ] + W[j  ] + a),  7) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(d, AND(b, XOR(c, d))) + (K[j+1] + W[j+1] + a), 12) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(d, AND(b, XOR(c, d))) + (K[j+2] + W[j+2] + a), 17) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(d, AND(b, XOR(c, d))) + (K[j+3] + W[j+3] + a), 22) + b)
         end
         for j = 17, 32, 4 do
            local g = 5*j-4
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, AND(d, XOR(b, c))) + (K[j  ] + W[AND(g     , 15) + 1] + a),  5) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, AND(d, XOR(b, c))) + (K[j+1] + W[AND(g +  5, 15) + 1] + a),  9) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, AND(d, XOR(b, c))) + (K[j+2] + W[AND(g + 10, 15) + 1] + a), 14) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, AND(d, XOR(b, c))) + (K[j+3] + W[AND(g -  1, 15) + 1] + a), 20) + b)
         end
         for j = 33, 48, 4 do
            local g = 3*j+2
            a, d, c, b = d, c, b, NORM(ROL(XOR(b, c, d) + (K[j  ] + W[AND(g    , 15) + 1] + a),  4) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(b, c, d) + (K[j+1] + W[AND(g + 3, 15) + 1] + a), 11) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(b, c, d) + (K[j+2] + W[AND(g + 6, 15) + 1] + a), 16) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(b, c, d) + (K[j+3] + W[AND(g - 7, 15) + 1] + a), 23) + b)
         end
         for j = 49, 64, 4 do
            local g = j*7
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, OR(b, NOT(d))) + (K[j  ] + W[AND(g - 7, 15) + 1] + a),  6) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, OR(b, NOT(d))) + (K[j+1] + W[AND(g    , 15) + 1] + a), 10) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, OR(b, NOT(d))) + (K[j+2] + W[AND(g + 7, 15) + 1] + a), 15) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, OR(b, NOT(d))) + (K[j+3] + W[AND(g - 2, 15) + 1] + a), 21) + b)
         end
         H[1], H[2], H[3], H[4] = NORM(a + H[1]), NORM(b + H[2]), NORM(c + H[3]), NORM(d + H[4])
      end
   end


   -- SHA-1 implementation for "LuaJIT without FFI" branch

   function sha1_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W = common_W
      for pos = offs, offs + size - 1, 64 do
         for j = 1, 16 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)
            W[j] = OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d)
         end
         for j = 17, 80 do
            W[j] = ROL(XOR(W[j-3], W[j-8], W[j-14], W[j-16]), 1)
         end
         local a, b, c, d, e = H[1], H[2], H[3], H[4], H[5]
         for j = 1, 20, 5 do
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j]   + 0x5A827999 + e))          -- constant = floor(2^30 * sqrt(2))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j+1] + 0x5A827999 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j+2] + 0x5A827999 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j+3] + 0x5A827999 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j+4] + 0x5A827999 + e))
         end
         for j = 21, 40, 5 do
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j]   + 0x6ED9EBA1 + e))                       -- 2^30 * sqrt(3)
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+1] + 0x6ED9EBA1 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+2] + 0x6ED9EBA1 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+3] + 0x6ED9EBA1 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+4] + 0x6ED9EBA1 + e))
         end
         for j = 41, 60, 5 do
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j]   + 0x8F1BBCDC + e))  -- 2^30 * sqrt(5)
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j+1] + 0x8F1BBCDC + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j+2] + 0x8F1BBCDC + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j+3] + 0x8F1BBCDC + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j+4] + 0x8F1BBCDC + e))
         end
         for j = 61, 80, 5 do
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j]   + 0xCA62C1D6 + e))                       -- 2^30 * sqrt(10)
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+1] + 0xCA62C1D6 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+2] + 0xCA62C1D6 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+3] + 0xCA62C1D6 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+4] + 0xCA62C1D6 + e))
         end
         H[1], H[2], H[3], H[4], H[5] = NORM(a + H[1]), NORM(b + H[2]), NORM(c + H[3]), NORM(d + H[4]), NORM(e + H[5])
      end
   end


   -- BLAKE2b implementation for "LuaJIT without FFI" branch

   do
      local v_lo, v_hi = {}, {}

      local function G(a, b, c, d, k1, k2)
         local W = common_W
         local va_lo, vb_lo, vc_lo, vd_lo = v_lo[a], v_lo[b], v_lo[c], v_lo[d]
         local va_hi, vb_hi, vc_hi, vd_hi = v_hi[a], v_hi[b], v_hi[c], v_hi[d]
         local z = W[2*k1-1] + (va_lo % 2^32 + vb_lo % 2^32)
         va_lo = NORM(z)
         va_hi = NORM(W[2*k1] + (va_hi + vb_hi + floor(z / 2^32)))
         vd_lo, vd_hi = XOR(vd_hi, va_hi), XOR(vd_lo, va_lo)
         z = vc_lo % 2^32 + vd_lo % 2^32
         vc_lo = NORM(z)
         vc_hi = NORM(vc_hi + vd_hi + floor(z / 2^32))
         vb_lo, vb_hi = XOR(vb_lo, vc_lo), XOR(vb_hi, vc_hi)
         vb_lo, vb_hi = XOR(SHR(vb_lo, 24), SHL(vb_hi, 8)), XOR(SHR(vb_hi, 24), SHL(vb_lo, 8))
         z = W[2*k2-1] + (va_lo % 2^32 + vb_lo % 2^32)
         va_lo = NORM(z)
         va_hi = NORM(W[2*k2] + (va_hi + vb_hi + floor(z / 2^32)))
         vd_lo, vd_hi = XOR(vd_lo, va_lo), XOR(vd_hi, va_hi)
         vd_lo, vd_hi = XOR(SHR(vd_lo, 16), SHL(vd_hi, 16)), XOR(SHR(vd_hi, 16), SHL(vd_lo, 16))
         z = vc_lo % 2^32 + vd_lo % 2^32
         vc_lo = NORM(z)
         vc_hi = NORM(vc_hi + vd_hi + floor(z / 2^32))
         vb_lo, vb_hi = XOR(vb_lo, vc_lo), XOR(vb_hi, vc_hi)
         vb_lo, vb_hi = XOR(SHL(vb_lo, 1), SHR(vb_hi, 31)), XOR(SHL(vb_hi, 1), SHR(vb_lo, 31))
         v_lo[a], v_lo[b], v_lo[c], v_lo[d] = va_lo, vb_lo, vc_lo, vd_lo
         v_hi[a], v_hi[b], v_hi[c], v_hi[d] = va_hi, vb_hi, vc_hi, vd_hi
      end

      function blake2b_feed_128(H_lo, H_hi, str, offs, size, bytes_compressed, last_block_size, is_last_node)
         -- offs >= 0, size >= 0, size is multiple of 128
         local W = common_W
         local h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo = H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8]
         local h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi = H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8]
         for pos = offs, offs + size - 1, 128 do
            if str then
               for j = 1, 32 do
                  pos = pos + 4
                  local a, b, c, d = byte(str, pos - 3, pos)
                  W[j] = d * 2^24 + OR(SHL(c, 16), SHL(b, 8), a)
               end
            end
            v_lo[0x0], v_lo[0x1], v_lo[0x2], v_lo[0x3], v_lo[0x4], v_lo[0x5], v_lo[0x6], v_lo[0x7] = h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo
            v_lo[0x8], v_lo[0x9], v_lo[0xA], v_lo[0xB], v_lo[0xC], v_lo[0xD], v_lo[0xE], v_lo[0xF] = sha2_H_lo[1], sha2_H_lo[2], sha2_H_lo[3], sha2_H_lo[4], sha2_H_lo[5], sha2_H_lo[6], sha2_H_lo[7], sha2_H_lo[8]
            v_hi[0x0], v_hi[0x1], v_hi[0x2], v_hi[0x3], v_hi[0x4], v_hi[0x5], v_hi[0x6], v_hi[0x7] = h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi
            v_hi[0x8], v_hi[0x9], v_hi[0xA], v_hi[0xB], v_hi[0xC], v_hi[0xD], v_hi[0xE], v_hi[0xF] = sha2_H_hi[1], sha2_H_hi[2], sha2_H_hi[3], sha2_H_hi[4], sha2_H_hi[5], sha2_H_hi[6], sha2_H_hi[7], sha2_H_hi[8]
            bytes_compressed = bytes_compressed + (last_block_size or 128)
            local t0_lo = bytes_compressed % 2^32
            local t0_hi = floor(bytes_compressed / 2^32)
            v_lo[0xC] = XOR(v_lo[0xC], t0_lo)  -- t0 = low_8_bytes(bytes_compressed)
            v_hi[0xC] = XOR(v_hi[0xC], t0_hi)
            -- t1 = high_8_bytes(bytes_compressed) = 0,  message length is always below 2^53 bytes
            if last_block_size then  -- flag f0
               v_lo[0xE] = NOT(v_lo[0xE])
               v_hi[0xE] = NOT(v_hi[0xE])
            end
            if is_last_node then  -- flag f1
               v_lo[0xF] = NOT(v_lo[0xF])
               v_hi[0xF] = NOT(v_hi[0xF])
            end
            for j = 1, 12 do
               local row = sigma[j]
               G(0, 4,  8, 12, row[ 1], row[ 2])
               G(1, 5,  9, 13, row[ 3], row[ 4])
               G(2, 6, 10, 14, row[ 5], row[ 6])
               G(3, 7, 11, 15, row[ 7], row[ 8])
               G(0, 5, 10, 15, row[ 9], row[10])
               G(1, 6, 11, 12, row[11], row[12])
               G(2, 7,  8, 13, row[13], row[14])
               G(3, 4,  9, 14, row[15], row[16])
            end
            h1_lo = XOR(h1_lo, v_lo[0x0], v_lo[0x8])
            h2_lo = XOR(h2_lo, v_lo[0x1], v_lo[0x9])
            h3_lo = XOR(h3_lo, v_lo[0x2], v_lo[0xA])
            h4_lo = XOR(h4_lo, v_lo[0x3], v_lo[0xB])
            h5_lo = XOR(h5_lo, v_lo[0x4], v_lo[0xC])
            h6_lo = XOR(h6_lo, v_lo[0x5], v_lo[0xD])
            h7_lo = XOR(h7_lo, v_lo[0x6], v_lo[0xE])
            h8_lo = XOR(h8_lo, v_lo[0x7], v_lo[0xF])
            h1_hi = XOR(h1_hi, v_hi[0x0], v_hi[0x8])
            h2_hi = XOR(h2_hi, v_hi[0x1], v_hi[0x9])
            h3_hi = XOR(h3_hi, v_hi[0x2], v_hi[0xA])
            h4_hi = XOR(h4_hi, v_hi[0x3], v_hi[0xB])
            h5_hi = XOR(h5_hi, v_hi[0x4], v_hi[0xC])
            h6_hi = XOR(h6_hi, v_hi[0x5], v_hi[0xD])
            h7_hi = XOR(h7_hi, v_hi[0x6], v_hi[0xE])
            h8_hi = XOR(h8_hi, v_hi[0x7], v_hi[0xF])
         end
         H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8] = h1_lo % 2^32, h2_lo % 2^32, h3_lo % 2^32, h4_lo % 2^32, h5_lo % 2^32, h6_lo % 2^32, h7_lo % 2^32, h8_lo % 2^32
         H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8] = h1_hi % 2^32, h2_hi % 2^32, h3_hi % 2^32, h4_hi % 2^32, h5_hi % 2^32, h6_hi % 2^32, h7_hi % 2^32, h8_hi % 2^32
         return bytes_compressed
      end

   end
end


if branch == "FFI" or branch == "LJ" then


   -- BLAKE2s and BLAKE3 implementations for "LuaJIT with FFI" and "LuaJIT without FFI" branches

   do
      local W = common_W_blake2s
      local v = v_for_blake2s_feed_64

      local function G(a, b, c, d, k1, k2)
         local va, vb, vc, vd = v[a], v[b], v[c], v[d]
         va = NORM(W[k1] + (va + vb))
         vd = ROR(XOR(vd, va), 16)
         vc = NORM(vc + vd)
         vb = ROR(XOR(vb, vc), 12)
         va = NORM(W[k2] + (va + vb))
         vd = ROR(XOR(vd, va), 8)
         vc = NORM(vc + vd)
         vb = ROR(XOR(vb, vc), 7)
         v[a], v[b], v[c], v[d] = va, vb, vc, vd
      end

      function blake2s_feed_64(H, str, offs, size, bytes_compressed, last_block_size, is_last_node)
         -- offs >= 0, size >= 0, size is multiple of 64
         local h1, h2, h3, h4, h5, h6, h7, h8 = NORM(H[1]), NORM(H[2]), NORM(H[3]), NORM(H[4]), NORM(H[5]), NORM(H[6]), NORM(H[7]), NORM(H[8])
         for pos = offs, offs + size - 1, 64 do
            if str then
               for j = 1, 16 do
                  pos = pos + 4
                  local a, b, c, d = byte(str, pos - 3, pos)
                  W[j] = OR(SHL(d, 24), SHL(c, 16), SHL(b, 8), a)
               end
            end
            v[0x0], v[0x1], v[0x2], v[0x3], v[0x4], v[0x5], v[0x6], v[0x7] = h1, h2, h3, h4, h5, h6, h7, h8
            v[0x8], v[0x9], v[0xA], v[0xB], v[0xE], v[0xF] = NORM(sha2_H_hi[1]), NORM(sha2_H_hi[2]), NORM(sha2_H_hi[3]), NORM(sha2_H_hi[4]), NORM(sha2_H_hi[7]), NORM(sha2_H_hi[8])
            bytes_compressed = bytes_compressed + (last_block_size or 64)
            local t0 = bytes_compressed % 2^32
            local t1 = floor(bytes_compressed / 2^32)
            v[0xC] = XOR(sha2_H_hi[5], t0)  -- t0 = low_4_bytes(bytes_compressed)
            v[0xD] = XOR(sha2_H_hi[6], t1)  -- t1 = high_4_bytes(bytes_compressed
            if last_block_size then  -- flag f0
               v[0xE] = NOT(v[0xE])
            end
            if is_last_node then  -- flag f1
               v[0xF] = NOT(v[0xF])
            end
            for j = 1, 10 do
               local row = sigma[j]
               G(0, 4,  8, 12, row[ 1], row[ 2])
               G(1, 5,  9, 13, row[ 3], row[ 4])
               G(2, 6, 10, 14, row[ 5], row[ 6])
               G(3, 7, 11, 15, row[ 7], row[ 8])
               G(0, 5, 10, 15, row[ 9], row[10])
               G(1, 6, 11, 12, row[11], row[12])
               G(2, 7,  8, 13, row[13], row[14])
               G(3, 4,  9, 14, row[15], row[16])
            end
            h1 = XOR(h1, v[0x0], v[0x8])
            h2 = XOR(h2, v[0x1], v[0x9])
            h3 = XOR(h3, v[0x2], v[0xA])
            h4 = XOR(h4, v[0x3], v[0xB])
            h5 = XOR(h5, v[0x4], v[0xC])
            h6 = XOR(h6, v[0x5], v[0xD])
            h7 = XOR(h7, v[0x6], v[0xE])
            h8 = XOR(h8, v[0x7], v[0xF])
         end
         H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8] = h1, h2, h3, h4, h5, h6, h7, h8
         return bytes_compressed
      end

      function blake3_feed_64(str, offs, size, flags, chunk_index, H_in, H_out, wide_output, block_length)
         -- offs >= 0, size >= 0, size is multiple of 64
         block_length = block_length or 64
         local h1, h2, h3, h4, h5, h6, h7, h8 = NORM(H_in[1]), NORM(H_in[2]), NORM(H_in[3]), NORM(H_in[4]), NORM(H_in[5]), NORM(H_in[6]), NORM(H_in[7]), NORM(H_in[8])
         H_out = H_out or H_in
         for pos = offs, offs + size - 1, 64 do
            if str then
               for j = 1, 16 do
                  pos = pos + 4
                  local a, b, c, d = byte(str, pos - 3, pos)
                  W[j] = OR(SHL(d, 24), SHL(c, 16), SHL(b, 8), a)
               end
            end
            v[0x0], v[0x1], v[0x2], v[0x3], v[0x4], v[0x5], v[0x6], v[0x7] = h1, h2, h3, h4, h5, h6, h7, h8
            v[0x8], v[0x9], v[0xA], v[0xB] = NORM(sha2_H_hi[1]), NORM(sha2_H_hi[2]), NORM(sha2_H_hi[3]), NORM(sha2_H_hi[4])
            v[0xC] = NORM(chunk_index % 2^32)   -- t0 = low_4_bytes(chunk_index)
            v[0xD] = floor(chunk_index / 2^32)  -- t1 = high_4_bytes(chunk_index)
            v[0xE], v[0xF] = block_length, flags
            for j = 1, 7 do
               G(0, 4,  8, 12, perm_blake3[j],      perm_blake3[j + 14])
               G(1, 5,  9, 13, perm_blake3[j + 1],  perm_blake3[j + 2])
               G(2, 6, 10, 14, perm_blake3[j + 16], perm_blake3[j + 7])
               G(3, 7, 11, 15, perm_blake3[j + 15], perm_blake3[j + 17])
               G(0, 5, 10, 15, perm_blake3[j + 21], perm_blake3[j + 5])
               G(1, 6, 11, 12, perm_blake3[j + 3],  perm_blake3[j + 6])
               G(2, 7,  8, 13, perm_blake3[j + 4],  perm_blake3[j + 18])
               G(3, 4,  9, 14, perm_blake3[j + 19], perm_blake3[j + 20])
            end
            if wide_output then
               H_out[ 9] = XOR(h1, v[0x8])
               H_out[10] = XOR(h2, v[0x9])
               H_out[11] = XOR(h3, v[0xA])
               H_out[12] = XOR(h4, v[0xB])
               H_out[13] = XOR(h5, v[0xC])
               H_out[14] = XOR(h6, v[0xD])
               H_out[15] = XOR(h7, v[0xE])
               H_out[16] = XOR(h8, v[0xF])
            end
            h1 = XOR(v[0x0], v[0x8])
            h2 = XOR(v[0x1], v[0x9])
            h3 = XOR(v[0x2], v[0xA])
            h4 = XOR(v[0x3], v[0xB])
            h5 = XOR(v[0x4], v[0xC])
            h6 = XOR(v[0x5], v[0xD])
            h7 = XOR(v[0x6], v[0xE])
            h8 = XOR(v[0x7], v[0xF])
         end
         H_out[1], H_out[2], H_out[3], H_out[4], H_out[5], H_out[6], H_out[7], H_out[8] = h1, h2, h3, h4, h5, h6, h7, h8
      end

   end

end


if branch == "INT64" then


   -- implementation for Lua 5.3/5.4

   hi_factor = 4294967296
   hi_factor_keccak = 4294967296
   lanes_index_base = 1

   HEX64, XORA5, XOR_BYTE, sha256_feed_64, sha512_feed_128, md5_feed_64, sha1_feed_64, keccak_feed, blake2s_feed_64, blake2b_feed_128, blake3_feed_64 = load[=[-- branch "INT64"
      local md5_next_shift, md5_K, sha2_K_lo, sha2_K_hi, build_keccak_format, sha3_RC_lo, sigma, common_W, sha2_H_lo, sha2_H_hi, perm_blake3 = ...
      local string_format, string_unpack = string.format, string.unpack

      local function HEX64(x)
         return string_format("%016x", x)
      end

      local function XORA5(x, y)
         return x ~ (y or 0xa5a5a5a5a5a5a5a5)
      end

      local function XOR_BYTE(x, y)
         return x ~ y
      end

      local function sha256_feed_64(H, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 64
         local W, K = common_W, sha2_K_hi
         local h1, h2, h3, h4, h5, h6, h7, h8 = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
         for pos = offs + 1, offs + size, 64 do
            W[1], W[2], W[3], W[4], W[5], W[6], W[7], W[8], W[9], W[10], W[11], W[12], W[13], W[14], W[15], W[16] =
               string_unpack(">I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4", str, pos)
            for j = 17, 64 do
               local a = W[j-15]
               a = a<<32 | a
               local b = W[j-2]
               b = b<<32 | b
               W[j] = (a>>7 ~ a>>18 ~ a>>35) + (b>>17 ~ b>>19 ~ b>>42) + W[j-7] + W[j-16] & (1<<32)-1
            end
            local a, b, c, d, e, f, g, h = h1, h2, h3, h4, h5, h6, h7, h8
            for j = 1, 64 do
               e = e<<32 | e & (1<<32)-1
               local z = (e>>6 ~ e>>11 ~ e>>25) + (g ~ e & (f ~ g)) + h + K[j] + W[j]
               h = g
               g = f
               f = e
               e = z + d
               d = c
               c = b
               b = a
               a = a<<32 | a & (1<<32)-1
               a = z + ((a ~ c) & d ~ a & c) + (a>>2 ~ a>>13 ~ a>>22)
            end
            h1 = a + h1
            h2 = b + h2
            h3 = c + h3
            h4 = d + h4
            h5 = e + h5
            h6 = f + h6
            h7 = g + h7
            h8 = h + h8
         end
         H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8] = h1, h2, h3, h4, h5, h6, h7, h8
      end

      local function sha512_feed_128(H, _, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 128
         local W, K = common_W, sha2_K_lo
         local h1, h2, h3, h4, h5, h6, h7, h8 = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
         for pos = offs + 1, offs + size, 128 do
            W[1], W[2], W[3], W[4], W[5], W[6], W[7], W[8], W[9], W[10], W[11], W[12], W[13], W[14], W[15], W[16] =
               string_unpack(">i8i8i8i8i8i8i8i8i8i8i8i8i8i8i8i8", str, pos)
            for j = 17, 80 do
               local a = W[j-15]
               local b = W[j-2]
               W[j] = (a >> 1 ~ a >> 7 ~ a >> 8 ~ a << 56 ~ a << 63) + (b >> 6 ~ b >> 19 ~ b >> 61 ~ b << 3 ~ b << 45) + W[j-7] + W[j-16]
            end
            local a, b, c, d, e, f, g, h = h1, h2, h3, h4, h5, h6, h7, h8
            for j = 1, 80 do
               local z = (e >> 14 ~ e >> 18 ~ e >> 41 ~ e << 23 ~ e << 46 ~ e << 50) + (g ~ e & (f ~ g)) + h + K[j] + W[j]
               h = g
               g = f
               f = e
               e = z + d
               d = c
               c = b
               b = a
               a = z + ((a ~ c) & d ~ a & c) + (a >> 28 ~ a >> 34 ~ a >> 39 ~ a << 25 ~ a << 30 ~ a << 36)
            end
            h1 = a + h1
            h2 = b + h2
            h3 = c + h3
            h4 = d + h4
            h5 = e + h5
            h6 = f + h6
            h7 = g + h7
            h8 = h + h8
         end
         H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8] = h1, h2, h3, h4, h5, h6, h7, h8
      end

      local function md5_feed_64(H, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 64
         local W, K, md5_next_shift = common_W, md5_K, md5_next_shift
         local h1, h2, h3, h4 = H[1], H[2], H[3], H[4]
         for pos = offs + 1, offs + size, 64 do
            W[1], W[2], W[3], W[4], W[5], W[6], W[7], W[8], W[9], W[10], W[11], W[12], W[13], W[14], W[15], W[16] =
               string_unpack("<I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4", str, pos)
            local a, b, c, d = h1, h2, h3, h4
            local s = 32-7
            for j = 1, 16 do
               local F = (d ~ b & (c ~ d)) + a + K[j] + W[j]
               a = d
               d = c
               c = b
               b = ((F<<32 | F & (1<<32)-1) >> s) + b
               s = md5_next_shift[s]
            end
            s = 32-5
            for j = 17, 32 do
               local F = (c ~ d & (b ~ c)) + a + K[j] + W[(5*j-4 & 15) + 1]
               a = d
               d = c
               c = b
               b = ((F<<32 | F & (1<<32)-1) >> s) + b
               s = md5_next_shift[s]
            end
            s = 32-4
            for j = 33, 48 do
               local F = (b ~ c ~ d) + a + K[j] + W[(3*j+2 & 15) + 1]
               a = d
               d = c
               c = b
               b = ((F<<32 | F & (1<<32)-1) >> s) + b
               s = md5_next_shift[s]
            end
            s = 32-6
            for j = 49, 64 do
               local F = (c ~ (b | ~d)) + a + K[j] + W[(j*7-7 & 15) + 1]
               a = d
               d = c
               c = b
               b = ((F<<32 | F & (1<<32)-1) >> s) + b
               s = md5_next_shift[s]
            end
            h1 = a + h1
            h2 = b + h2
            h3 = c + h3
            h4 = d + h4
         end
         H[1], H[2], H[3], H[4] = h1, h2, h3, h4
      end

      local function sha1_feed_64(H, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 64
         local W = common_W
         local h1, h2, h3, h4, h5 = H[1], H[2], H[3], H[4], H[5]
         for pos = offs + 1, offs + size, 64 do
            W[1], W[2], W[3], W[4], W[5], W[6], W[7], W[8], W[9], W[10], W[11], W[12], W[13], W[14], W[15], W[16] =
               string_unpack(">I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4", str, pos)
            for j = 17, 80 do
               local a = W[j-3] ~ W[j-8] ~ W[j-14] ~ W[j-16]
               W[j] = (a<<32 | a) << 1 >> 32
            end
            local a, b, c, d, e = h1, h2, h3, h4, h5
            for j = 1, 20 do
               local z = ((a<<32 | a & (1<<32)-1) >> 27) + (d ~ b & (c ~ d)) + 0x5A827999 + W[j] + e      -- constant = floor(2^30 * sqrt(2))
               e = d
               d = c
               c = (b<<32 | b & (1<<32)-1) >> 2
               b = a
               a = z
            end
            for j = 21, 40 do
               local z = ((a<<32 | a & (1<<32)-1) >> 27) + (b ~ c ~ d) + 0x6ED9EBA1 + W[j] + e            -- 2^30 * sqrt(3)
               e = d
               d = c
               c = (b<<32 | b & (1<<32)-1) >> 2
               b = a
               a = z
            end
            for j = 41, 60 do
               local z = ((a<<32 | a & (1<<32)-1) >> 27) + ((b ~ c) & d ~ b & c) + 0x8F1BBCDC + W[j] + e  -- 2^30 * sqrt(5)
               e = d
               d = c
               c = (b<<32 | b & (1<<32)-1) >> 2
               b = a
               a = z
            end
            for j = 61, 80 do
               local z = ((a<<32 | a & (1<<32)-1) >> 27) + (b ~ c ~ d) + 0xCA62C1D6 + W[j] + e            -- 2^30 * sqrt(10)
               e = d
               d = c
               c = (b<<32 | b & (1<<32)-1) >> 2
               b = a
               a = z
            end
            h1 = a + h1
            h2 = b + h2
            h3 = c + h3
            h4 = d + h4
            h5 = e + h5
         end
         H[1], H[2], H[3], H[4], H[5] = h1, h2, h3, h4, h5
      end

      local keccak_format_i8 = build_keccak_format("i8")

      local function keccak_feed(lanes, _, str, offs, size, block_size_in_bytes)
         -- offs >= 0, size >= 0, size is multiple of block_size_in_bytes, block_size_in_bytes is positive multiple of 8
         local RC = sha3_RC_lo
         local qwords_qty = block_size_in_bytes / 8
         local keccak_format = keccak_format_i8[qwords_qty]
         for pos = offs + 1, offs + size, block_size_in_bytes do
            local qwords_from_message = {string_unpack(keccak_format, str, pos)}
            for j = 1, qwords_qty do
               lanes[j] = lanes[j] ~ qwords_from_message[j]
            end
            local L01, L02, L03, L04, L05, L06, L07, L08, L09, L10, L11, L12, L13, L14, L15, L16, L17, L18, L19, L20, L21, L22, L23, L24, L25 =
               lanes[1], lanes[2], lanes[3], lanes[4], lanes[5], lanes[6], lanes[7], lanes[8], lanes[9], lanes[10], lanes[11], lanes[12], lanes[13],
               lanes[14], lanes[15], lanes[16], lanes[17], lanes[18], lanes[19], lanes[20], lanes[21], lanes[22], lanes[23], lanes[24], lanes[25]
            for round_idx = 1, 24 do
               local C1 = L01 ~ L06 ~ L11 ~ L16 ~ L21
               local C2 = L02 ~ L07 ~ L12 ~ L17 ~ L22
               local C3 = L03 ~ L08 ~ L13 ~ L18 ~ L23
               local C4 = L04 ~ L09 ~ L14 ~ L19 ~ L24
               local C5 = L05 ~ L10 ~ L15 ~ L20 ~ L25
               local D = C1 ~ C3<<1 ~ C3>>63
               local T0 = D ~ L02
               local T1 = D ~ L07
               local T2 = D ~ L12
               local T3 = D ~ L17
               local T4 = D ~ L22
               L02 = T1<<44 ~ T1>>20
               L07 = T3<<45 ~ T3>>19
               L12 = T0<<1 ~ T0>>63
               L17 = T2<<10 ~ T2>>54
               L22 = T4<<2 ~ T4>>62
               D = C2 ~ C4<<1 ~ C4>>63
               T0 = D ~ L03
               T1 = D ~ L08
               T2 = D ~ L13
               T3 = D ~ L18
               T4 = D ~ L23
               L03 = T2<<43 ~ T2>>21
               L08 = T4<<61 ~ T4>>3
               L13 = T1<<6 ~ T1>>58
               L18 = T3<<15 ~ T3>>49
               L23 = T0<<62 ~ T0>>2
               D = C3 ~ C5<<1 ~ C5>>63
               T0 = D ~ L04
               T1 = D ~ L09
               T2 = D ~ L14
               T3 = D ~ L19
               T4 = D ~ L24
               L04 = T3<<21 ~ T3>>43
               L09 = T0<<28 ~ T0>>36
               L14 = T2<<25 ~ T2>>39
               L19 = T4<<56 ~ T4>>8
               L24 = T1<<55 ~ T1>>9
               D = C4 ~ C1<<1 ~ C1>>63
               T0 = D ~ L05
               T1 = D ~ L10
               T2 = D ~ L15
               T3 = D ~ L20
               T4 = D ~ L25
               L05 = T4<<14 ~ T4>>50
               L10 = T1<<20 ~ T1>>44
               L15 = T3<<8 ~ T3>>56
               L20 = T0<<27 ~ T0>>37
               L25 = T2<<39 ~ T2>>25
               D = C5 ~ C2<<1 ~ C2>>63
               T1 = D ~ L06
               T2 = D ~ L11
               T3 = D ~ L16
               T4 = D ~ L21
               L06 = T2<<3 ~ T2>>61
               L11 = T4<<18 ~ T4>>46
               L16 = T1<<36 ~ T1>>28
               L21 = T3<<41 ~ T3>>23
               L01 = D ~ L01
               L01, L02, L03, L04, L05 = L01 ~ ~L02 & L03, L02 ~ ~L03 & L04, L03 ~ ~L04 & L05, L04 ~ ~L05 & L01, L05 ~ ~L01 & L02
               L06, L07, L08, L09, L10 = L09 ~ ~L10 & L06, L10 ~ ~L06 & L07, L06 ~ ~L07 & L08, L07 ~ ~L08 & L09, L08 ~ ~L09 & L10
               L11, L12, L13, L14, L15 = L12 ~ ~L13 & L14, L13 ~ ~L14 & L15, L14 ~ ~L15 & L11, L15 ~ ~L11 & L12, L11 ~ ~L12 & L13
               L16, L17, L18, L19, L20 = L20 ~ ~L16 & L17, L16 ~ ~L17 & L18, L17 ~ ~L18 & L19, L18 ~ ~L19 & L20, L19 ~ ~L20 & L16
               L21, L22, L23, L24, L25 = L23 ~ ~L24 & L25, L24 ~ ~L25 & L21, L25 ~ ~L21 & L22, L21 ~ ~L22 & L23, L22 ~ ~L23 & L24
               L01 = L01 ~ RC[round_idx]
            end
            lanes[1]  = L01
            lanes[2]  = L02
            lanes[3]  = L03
            lanes[4]  = L04
            lanes[5]  = L05
            lanes[6]  = L06
            lanes[7]  = L07
            lanes[8]  = L08
            lanes[9]  = L09
            lanes[10] = L10
            lanes[11] = L11
            lanes[12] = L12
            lanes[13] = L13
            lanes[14] = L14
            lanes[15] = L15
            lanes[16] = L16
            lanes[17] = L17
            lanes[18] = L18
            lanes[19] = L19
            lanes[20] = L20
            lanes[21] = L21
            lanes[22] = L22
            lanes[23] = L23
            lanes[24] = L24
            lanes[25] = L25
         end
      end

      local function blake2s_feed_64(H, str, offs, size, bytes_compressed, last_block_size, is_last_node)
         -- offs >= 0, size >= 0, size is multiple of 64
         local W = common_W
         local h1, h2, h3, h4, h5, h6, h7, h8 = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
         for pos = offs + 1, offs + size, 64 do
            if str then
               W[1], W[2], W[3], W[4], W[5], W[6], W[7], W[8], W[9], W[10], W[11], W[12], W[13], W[14], W[15], W[16] =
                  string_unpack("<I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4", str, pos)
            end
            local v0, v1, v2, v3, v4, v5, v6, v7 = h1, h2, h3, h4, h5, h6, h7, h8
            local v8, v9, vA, vB, vC, vD, vE, vF = sha2_H_hi[1], sha2_H_hi[2], sha2_H_hi[3], sha2_H_hi[4], sha2_H_hi[5], sha2_H_hi[6], sha2_H_hi[7], sha2_H_hi[8]
            bytes_compressed = bytes_compressed + (last_block_size or 64)
            vC = vC ~ bytes_compressed        -- t0 = low_4_bytes(bytes_compressed)
            vD = vD ~ bytes_compressed >> 32  -- t1 = high_4_bytes(bytes_compressed)
            if last_block_size then  -- flag f0
               vE = ~vE
            end
            if is_last_node then  -- flag f1
               vF = ~vF
            end
            for j = 1, 10 do
               local row = sigma[j]
               v0 = v0 + v4 + W[row[1]]
               vC = vC ~ v0
               vC = (vC & (1<<32)-1) >> 16 | vC << 16
               v8 = v8 + vC
               v4 = v4 ~ v8
               v4 = (v4 & (1<<32)-1) >> 12 | v4 << 20
               v0 = v0 + v4 + W[row[2]]
               vC = vC ~ v0
               vC = (vC & (1<<32)-1) >> 8 | vC << 24
               v8 = v8 + vC
               v4 = v4 ~ v8
               v4 = (v4 & (1<<32)-1) >> 7 | v4 << 25
               v1 = v1 + v5 + W[row[3]]
               vD = vD ~ v1
               vD = (vD & (1<<32)-1) >> 16 | vD << 16
               v9 = v9 + vD
               v5 = v5 ~ v9
               v5 = (v5 & (1<<32)-1) >> 12 | v5 << 20
               v1 = v1 + v5 + W[row[4]]
               vD = vD ~ v1
               vD = (vD & (1<<32)-1) >> 8 | vD << 24
               v9 = v9 + vD
               v5 = v5 ~ v9
               v5 = (v5 & (1<<32)-1) >> 7 | v5 << 25
               v2 = v2 + v6 + W[row[5]]
               vE = vE ~ v2
               vE = (vE & (1<<32)-1) >> 16 | vE << 16
               vA = vA + vE
               v6 = v6 ~ vA
               v6 = (v6 & (1<<32)-1) >> 12 | v6 << 20
               v2 = v2 + v6 + W[row[6]]
               vE = vE ~ v2
               vE = (vE & (1<<32)-1) >> 8 | vE << 24
               vA = vA + vE
               v6 = v6 ~ vA
               v6 = (v6 & (1<<32)-1) >> 7 | v6 << 25
               v3 = v3 + v7 + W[row[7]]
               vF = vF ~ v3
               vF = (vF & (1<<32)-1) >> 16 | vF << 16
               vB = vB + vF
               v7 = v7 ~ vB
               v7 = (v7 & (1<<32)-1) >> 12 | v7 << 20
               v3 = v3 + v7 + W[row[8]]
               vF = vF ~ v3
               vF = (vF & (1<<32)-1) >> 8 | vF << 24
               vB = vB + vF
               v7 = v7 ~ vB
               v7 = (v7 & (1<<32)-1) >> 7 | v7 << 25
               v0 = v0 + v5 + W[row[9]]
               vF = vF ~ v0
               vF = (vF & (1<<32)-1) >> 16 | vF << 16
               vA = vA + vF
               v5 = v5 ~ vA
               v5 = (v5 & (1<<32)-1) >> 12 | v5 << 20
               v0 = v0 + v5 + W[row[10]]
               vF = vF ~ v0
               vF = (vF & (1<<32)-1) >> 8 | vF << 24
               vA = vA + vF
               v5 = v5 ~ vA
               v5 = (v5 & (1<<32)-1) >> 7 | v5 << 25
               v1 = v1 + v6 + W[row[11]]
               vC = vC ~ v1
               vC = (vC & (1<<32)-1) >> 16 | vC << 16
               vB = vB + vC
               v6 = v6 ~ vB
               v6 = (v6 & (1<<32)-1) >> 12 | v6 << 20
               v1 = v1 + v6 + W[row[12]]
               vC = vC ~ v1
               vC = (vC & (1<<32)-1) >> 8 | vC << 24
               vB = vB + vC
               v6 = v6 ~ vB
               v6 = (v6 & (1<<32)-1) >> 7 | v6 << 25
               v2 = v2 + v7 + W[row[13]]
               vD = vD ~ v2
               vD = (vD & (1<<32)-1) >> 16 | vD << 16
               v8 = v8 + vD
               v7 = v7 ~ v8
               v7 = (v7 & (1<<32)-1) >> 12 | v7 << 20
               v2 = v2 + v7 + W[row[14]]
               vD = vD ~ v2
               vD = (vD & (1<<32)-1) >> 8 | vD << 24
               v8 = v8 + vD
               v7 = v7 ~ v8
               v7 = (v7 & (1<<32)-1) >> 7 | v7 << 25
               v3 = v3 + v4 + W[row[15]]
               vE = vE ~ v3
               vE = (vE & (1<<32)-1) >> 16 | vE << 16
               v9 = v9 + vE
               v4 = v4 ~ v9
               v4 = (v4 & (1<<32)-1) >> 12 | v4 << 20
               v3 = v3 + v4 + W[row[16]]
               vE = vE ~ v3
               vE = (vE & (1<<32)-1) >> 8 | vE << 24
               v9 = v9 + vE
               v4 = v4 ~ v9
               v4 = (v4 & (1<<32)-1) >> 7 | v4 << 25
            end
            h1 = h1 ~ v0 ~ v8
            h2 = h2 ~ v1 ~ v9
            h3 = h3 ~ v2 ~ vA
            h4 = h4 ~ v3 ~ vB
            h5 = h5 ~ v4 ~ vC
            h6 = h6 ~ v5 ~ vD
            h7 = h7 ~ v6 ~ vE
            h8 = h8 ~ v7 ~ vF
         end
         H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8] = h1, h2, h3, h4, h5, h6, h7, h8
         return bytes_compressed
      end

      local function blake2b_feed_128(H, _, str, offs, size, bytes_compressed, last_block_size, is_last_node)
         -- offs >= 0, size >= 0, size is multiple of 128
         local W = common_W
         local h1, h2, h3, h4, h5, h6, h7, h8 = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
         for pos = offs + 1, offs + size, 128 do
            if str then
               W[1], W[2], W[3], W[4], W[5], W[6], W[7], W[8], W[9], W[10], W[11], W[12], W[13], W[14], W[15], W[16] =
                  string_unpack("<i8i8i8i8i8i8i8i8i8i8i8i8i8i8i8i8", str, pos)
            end
            local v0, v1, v2, v3, v4, v5, v6, v7 = h1, h2, h3, h4, h5, h6, h7, h8
            local v8, v9, vA, vB, vC, vD, vE, vF = sha2_H_lo[1], sha2_H_lo[2], sha2_H_lo[3], sha2_H_lo[4], sha2_H_lo[5], sha2_H_lo[6], sha2_H_lo[7], sha2_H_lo[8]
            bytes_compressed = bytes_compressed + (last_block_size or 128)
            vC = vC ~ bytes_compressed  -- t0 = low_8_bytes(bytes_compressed)
            -- t1 = high_8_bytes(bytes_compressed) = 0,  message length is always below 2^53 bytes
            if last_block_size then  -- flag f0
               vE = ~vE
            end
            if is_last_node then  -- flag f1
               vF = ~vF
            end
            for j = 1, 12 do
               local row = sigma[j]
               v0 = v0 + v4 + W[row[1]]
               vC = vC ~ v0
               vC = vC >> 32 | vC << 32
               v8 = v8 + vC
               v4 = v4 ~ v8
               v4 = v4 >> 24 | v4 << 40
               v0 = v0 + v4 + W[row[2]]
               vC = vC ~ v0
               vC = vC >> 16 | vC << 48
               v8 = v8 + vC
               v4 = v4 ~ v8
               v4 = v4 >> 63 | v4 << 1
               v1 = v1 + v5 + W[row[3]]
               vD = vD ~ v1
               vD = vD >> 32 | vD << 32
               v9 = v9 + vD
               v5 = v5 ~ v9
               v5 = v5 >> 24 | v5 << 40
               v1 = v1 + v5 + W[row[4]]
               vD = vD ~ v1
               vD = vD >> 16 | vD << 48
               v9 = v9 + vD
               v5 = v5 ~ v9
               v5 = v5 >> 63 | v5 << 1
               v2 = v2 + v6 + W[row[5]]
               vE = vE ~ v2
               vE = vE >> 32 | vE << 32
               vA = vA + vE
               v6 = v6 ~ vA
               v6 = v6 >> 24 | v6 << 40
               v2 = v2 + v6 + W[row[6]]
               vE = vE ~ v2
               vE = vE >> 16 | vE << 48
               vA = vA + vE
               v6 = v6 ~ vA
               v6 = v6 >> 63 | v6 << 1
               v3 = v3 + v7 + W[row[7]]
               vF = vF ~ v3
               vF = vF >> 32 | vF << 32
               vB = vB + vF
               v7 = v7 ~ vB
               v7 = v7 >> 24 | v7 << 40
               v3 = v3 + v7 + W[row[8]]
               vF = vF ~ v3
               vF = vF >> 16 | vF << 48
               vB = vB + vF
               v7 = v7 ~ vB
               v7 = v7 >> 63 | v7 << 1
               v0 = v0 + v5 + W[row[9]]
               vF = vF ~ v0
               vF = vF >> 32 | vF << 32
               vA = vA + vF
               v5 = v5 ~ vA
               v5 = v5 >> 24 | v5 << 40
               v0 = v0 + v5 + W[row[10]]
               vF = vF ~ v0
               vF = vF >> 16 | vF << 48
               vA = vA + vF
               v5 = v5 ~ vA
               v5 = v5 >> 63 | v5 << 1
               v1 = v1 + v6 + W[row[11]]
               vC = vC ~ v1
               vC = vC >> 32 | vC << 32
               vB = vB + vC
               v6 = v6 ~ vB
               v6 = v6 >> 24 | v6 << 40
               v1 = v1 + v6 + W[row[12]]
               vC = vC ~ v1
               vC = vC >> 16 | vC << 48
               vB = vB + vC
               v6 = v6 ~ vB
               v6 = v6 >> 63 | v6 << 1
               v2 = v2 + v7 + W[row[13]]
               vD = vD ~ v2
               vD = vD >> 32 | vD << 32
               v8 = v8 + vD
               v7 = v7 ~ v8
               v7 = v7 >> 24 | v7 << 40
               v2 = v2 + v7 + W[row[14]]
               vD = vD ~ v2
               vD = vD >> 16 | vD << 48
               v8 = v8 + vD
               v7 = v7 ~ v8
               v7 = v7 >> 63 | v7 << 1
               v3 = v3 + v4 + W[row[15]]
               vE = vE ~ v3
               vE = vE >> 32 | vE << 32
               v9 = v9 + vE
               v4 = v4 ~ v9
               v4 = v4 >> 24 | v4 << 40
               v3 = v3 + v4 + W[row[16]]
               vE = vE ~ v3
               vE = vE >> 16 | vE << 48
               v9 = v9 + vE
               v4 = v4 ~ v9
               v4 = v4 >> 63 | v4 << 1
            end
            h1 = h1 ~ v0 ~ v8
            h2 = h2 ~ v1 ~ v9
            h3 = h3 ~ v2 ~ vA
            h4 = h4 ~ v3 ~ vB
            h5 = h5 ~ v4 ~ vC
            h6 = h6 ~ v5 ~ vD
            h7 = h7 ~ v6 ~ vE
            h8 = h8 ~ v7 ~ vF
         end
         H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8] = h1, h2, h3, h4, h5, h6, h7, h8
         return bytes_compressed
      end

      local function blake3_feed_64(str, offs, size, flags, chunk_index, H_in, H_out, wide_output, block_length)
         -- offs >= 0, size >= 0, size is multiple of 64
         block_length = block_length or 64
         local W = common_W
         local h1, h2, h3, h4, h5, h6, h7, h8 = H_in[1], H_in[2], H_in[3], H_in[4], H_in[5], H_in[6], H_in[7], H_in[8]
         H_out = H_out or H_in
         for pos = offs + 1, offs + size, 64 do
            if str then
               W[1], W[2], W[3], W[4], W[5], W[6], W[7], W[8], W[9], W[10], W[11], W[12], W[13], W[14], W[15], W[16] =
                  string_unpack("<I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4", str, pos)
            end
            local v0, v1, v2, v3, v4, v5, v6, v7 = h1, h2, h3, h4, h5, h6, h7, h8
            local v8, v9, vA, vB = sha2_H_hi[1], sha2_H_hi[2], sha2_H_hi[3], sha2_H_hi[4]
            local t0 = chunk_index % 2^32         -- t0 = low_4_bytes(chunk_index)
            local t1 = (chunk_index - t0) / 2^32  -- t1 = high_4_bytes(chunk_index)
            local vC, vD, vE, vF = 0|t0, 0|t1, block_length, flags
            for j = 1, 7 do
               v0 = v0 + v4 + W[perm_blake3[j]]
               vC = vC ~ v0
               vC = (vC & (1<<32)-1) >> 16 | vC << 16
               v8 = v8 + vC
               v4 = v4 ~ v8
               v4 = (v4 & (1<<32)-1) >> 12 | v4 << 20
               v0 = v0 + v4 + W[perm_blake3[j + 14]]
               vC = vC ~ v0
               vC = (vC & (1<<32)-1) >> 8 | vC << 24
               v8 = v8 + vC
               v4 = v4 ~ v8
               v4 = (v4 & (1<<32)-1) >> 7 | v4 << 25
               v1 = v1 + v5 + W[perm_blake3[j + 1]]
               vD = vD ~ v1
               vD = (vD & (1<<32)-1) >> 16 | vD << 16
               v9 = v9 + vD
               v5 = v5 ~ v9
               v5 = (v5 & (1<<32)-1) >> 12 | v5 << 20
               v1 = v1 + v5 + W[perm_blake3[j + 2]]
               vD = vD ~ v1
               vD = (vD & (1<<32)-1) >> 8 | vD << 24
               v9 = v9 + vD
               v5 = v5 ~ v9
               v5 = (v5 & (1<<32)-1) >> 7 | v5 << 25
               v2 = v2 + v6 + W[perm_blake3[j + 16]]
               vE = vE ~ v2
               vE = (vE & (1<<32)-1) >> 16 | vE << 16
               vA = vA + vE
               v6 = v6 ~ vA
               v6 = (v6 & (1<<32)-1) >> 12 | v6 << 20
               v2 = v2 + v6 + W[perm_blake3[j + 7]]
               vE = vE ~ v2
               vE = (vE & (1<<32)-1) >> 8 | vE << 24
               vA = vA + vE
               v6 = v6 ~ vA
               v6 = (v6 & (1<<32)-1) >> 7 | v6 << 25
               v3 = v3 + v7 + W[perm_blake3[j + 15]]
               vF = vF ~ v3
               vF = (vF & (1<<32)-1) >> 16 | vF << 16
               vB = vB + vF
               v7 = v7 ~ vB
               v7 = (v7 & (1<<32)-1) >> 12 | v7 << 20
               v3 = v3 + v7 + W[perm_blake3[j + 17]]
               vF = vF ~ v3
               vF = (vF & (1<<32)-1) >> 8 | vF << 24
               vB = vB + vF
               v7 = v7 ~ vB
               v7 = (v7 & (1<<32)-1) >> 7 | v7 << 25
               v0 = v0 + v5 + W[perm_blake3[j + 21]]
               vF = vF ~ v0
               vF = (vF & (1<<32)-1) >> 16 | vF << 16
               vA = vA + vF
               v5 = v5 ~ vA
               v5 = (v5 & (1<<32)-1) >> 12 | v5 << 20
               v0 = v0 + v5 + W[perm_blake3[j + 5]]
               vF = vF ~ v0
               vF = (vF & (1<<32)-1) >> 8 | vF << 24
               vA = vA + vF
               v5 = v5 ~ vA
               v5 = (v5 & (1<<32)-1) >> 7 | v5 << 25
               v1 = v1 + v6 + W[perm_blake3[j + 3]]
               vC = vC ~ v1
               vC = (vC & (1<<32)-1) >> 16 | vC << 16
               vB = vB + vC
               v6 = v6 ~ vB
               v6 = (v6 & (1<<32)-1) >> 12 | v6 << 20
               v1 = v1 + v6 + W[perm_blake3[j + 6]]
               vC = vC ~ v1
               vC = (vC & (1<<32)-1) >> 8 | vC << 24
               vB = vB + vC
               v6 = v6 ~ vB
               v6 = (v6 & (1<<32)-1) >> 7 | v6 << 25
               v2 = v2 + v7 + W[perm_blake3[j + 4]]
               vD = vD ~ v2
               vD = (vD & (1<<32)-1) >> 16 | vD << 16
               v8 = v8 + vD
               v7 = v7 ~ v8
               v7 = (v7 & (1<<32)-1) >> 12 | v7 << 20
               v2 = v2 + v7 + W[perm_blake3[j + 18]]
               vD = vD ~ v2
               vD = (vD & (1<<32)-1) >> 8 | vD << 24
               v8 = v8 + vD
               v7 = v7 ~ v8
               v7 = (v7 & (1<<32)-1) >> 7 | v7 << 25
               v3 = v3 + v4 + W[perm_blake3[j + 19]]
               vE = vE ~ v3
               vE = (vE & (1<<32)-1) >> 16 | vE << 16
               v9 = v9 + vE
               v4 = v4 ~ v9
               v4 = (v4 & (1<<32)-1) >> 12 | v4 << 20
               v3 = v3 + v4 + W[perm_blake3[j + 20]]
               vE = vE ~ v3
               vE = (vE & (1<<32)-1) >> 8 | vE << 24
               v9 = v9 + vE
               v4 = v4 ~ v9
               v4 = (v4 & (1<<32)-1) >> 7 | v4 << 25
            end
            if wide_output then
               H_out[ 9] = h1 ~ v8
               H_out[10] = h2 ~ v9
               H_out[11] = h3 ~ vA
               H_out[12] = h4 ~ vB
               H_out[13] = h5 ~ vC
               H_out[14] = h6 ~ vD
               H_out[15] = h7 ~ vE
               H_out[16] = h8 ~ vF
            end
            h1 = v0 ~ v8
            h2 = v1 ~ v9
            h3 = v2 ~ vA
            h4 = v3 ~ vB
            h5 = v4 ~ vC
            h6 = v5 ~ vD
            h7 = v6 ~ vE
            h8 = v7 ~ vF
         end
         H_out[1], H_out[2], H_out[3], H_out[4], H_out[5], H_out[6], H_out[7], H_out[8] = h1, h2, h3, h4, h5, h6, h7, h8
      end

      return HEX64, XORA5, XOR_BYTE, sha256_feed_64, sha512_feed_128, md5_feed_64, sha1_feed_64, keccak_feed, blake2s_feed_64, blake2b_feed_128, blake3_feed_64
   ]=](md5_next_shift, md5_K, sha2_K_lo, sha2_K_hi, build_keccak_format, sha3_RC_lo, sigma, common_W, sha2_H_lo, sha2_H_hi, perm_blake3)

end


if branch == "INT32" then


   -- implementation for Lua 5.3/5.4 having non-standard numbers config "int32"+"double" (built with LUA_INT_TYPE=LUA_INT_INT)

   K_lo_modulo = 2^32

   function HEX(x) -- returns string of 8 lowercase hexadecimal digits
      return string_format("%08x", x)
   end

   XORA5, XOR_BYTE, sha256_feed_64, sha512_feed_128, md5_feed_64, sha1_feed_64, keccak_feed, blake2s_feed_64, blake2b_feed_128, blake3_feed_64 = load[=[-- branch "INT32"
      local md5_next_shift, md5_K, sha2_K_lo, sha2_K_hi, build_keccak_format, sha3_RC_lo, sha3_RC_hi, sigma, common_W, sha2_H_lo, sha2_H_hi, perm_blake3 = ...
      local string_unpack, floor = string.unpack, math.floor

      local function XORA5(x, y)
         return x ~ (y and (y + 2^31) % 2^32 - 2^31 or 0xA5A5A5A5)
      end

      local function XOR_BYTE(x, y)
         return x ~ y
      end

      local function sha256_feed_64(H, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 64
         local W, K = common_W, sha2_K_hi
         local h1, h2, h3, h4, h5, h6, h7, h8 = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
         for pos = offs + 1, offs + size, 64 do
            W[1], W[2], W[3], W[4], W[5], W[6], W[7], W[8], W[9], W[10], W[11], W[12], W[13], W[14], W[15], W[16] =
               string_unpack(">i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4", str, pos)
            for j = 17, 64 do
               local a, b = W[j-15], W[j-2]
               W[j] = (a>>7 ~ a<<25 ~ a<<14 ~ a>>18 ~ a>>3) + (b<<15 ~ b>>17 ~ b<<13 ~ b>>19 ~ b>>10) + W[j-7] + W[j-16]
            end
            local a, b, c, d, e, f, g, h = h1, h2, h3, h4, h5, h6, h7, h8
            for j = 1, 64 do
               local z = (e>>6 ~ e<<26 ~ e>>11 ~ e<<21 ~ e>>25 ~ e<<7) + (g ~ e & (f ~ g)) + h + K[j] + W[j]
               h = g
               g = f
               f = e
               e = z + d
               d = c
               c = b
               b = a
               a = z + ((a ~ c) & d ~ a & c) + (a>>2 ~ a<<30 ~ a>>13 ~ a<<19 ~ a<<10 ~ a>>22)
            end
            h1 = a + h1
            h2 = b + h2
            h3 = c + h3
            h4 = d + h4
            h5 = e + h5
            h6 = f + h6
            h7 = g + h7
            h8 = h + h8
         end
         H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8] = h1, h2, h3, h4, h5, h6, h7, h8
      end

      local function sha512_feed_128(H_lo, H_hi, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 128
         -- W1_hi, W1_lo, W2_hi, W2_lo, ...   Wk_hi = W[2*k-1], Wk_lo = W[2*k]
         local floor, W, K_lo, K_hi = floor, common_W, sha2_K_lo, sha2_K_hi
         local h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo = H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8]
         local h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi = H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8]
         for pos = offs + 1, offs + size, 128 do
            W[1], W[2], W[3], W[4], W[5], W[6], W[7], W[8], W[9], W[10], W[11], W[12], W[13], W[14], W[15], W[16],
               W[17], W[18], W[19], W[20], W[21], W[22], W[23], W[24], W[25], W[26], W[27], W[28], W[29], W[30], W[31], W[32] =
               string_unpack(">i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4", str, pos)
            for jj = 17*2, 80*2, 2 do
               local a_lo, a_hi, b_lo, b_hi = W[jj-30], W[jj-31], W[jj-4], W[jj-5]
               local tmp =
                  (a_lo>>1 ~ a_hi<<31 ~ a_lo>>8 ~ a_hi<<24 ~ a_lo>>7 ~ a_hi<<25) % 2^32
                  + (b_lo>>19 ~ b_hi<<13 ~ b_lo<<3 ~ b_hi>>29 ~ b_lo>>6 ~ b_hi<<26) % 2^32
                  + W[jj-14] % 2^32 + W[jj-32] % 2^32
               W[jj-1] =
                  (a_hi>>1 ~ a_lo<<31 ~ a_hi>>8 ~ a_lo<<24 ~ a_hi>>7)
                  + (b_hi>>19 ~ b_lo<<13 ~ b_hi<<3 ~ b_lo>>29 ~ b_hi>>6)
                  + W[jj-15] + W[jj-33] + floor(tmp / 2^32)
               W[jj] = 0|((tmp + 2^31) % 2^32 - 2^31)
            end
            local a_lo, b_lo, c_lo, d_lo, e_lo, f_lo, g_lo, h_lo = h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo
            local a_hi, b_hi, c_hi, d_hi, e_hi, f_hi, g_hi, h_hi = h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi
            for j = 1, 80 do
               local jj = 2*j
               local z_lo = (e_lo>>14 ~ e_hi<<18 ~ e_lo>>18 ~ e_hi<<14 ~ e_lo<<23 ~ e_hi>>9) % 2^32 + (g_lo ~ e_lo & (f_lo ~ g_lo)) % 2^32 + h_lo % 2^32 + K_lo[j] + W[jj] % 2^32
               local z_hi = (e_hi>>14 ~ e_lo<<18 ~ e_hi>>18 ~ e_lo<<14 ~ e_hi<<23 ~ e_lo>>9) + (g_hi ~ e_hi & (f_hi ~ g_hi)) + h_hi + K_hi[j] + W[jj-1] + floor(z_lo / 2^32)
               z_lo = z_lo % 2^32
               h_lo = g_lo;  h_hi = g_hi
               g_lo = f_lo;  g_hi = f_hi
               f_lo = e_lo;  f_hi = e_hi
               e_lo = z_lo + d_lo % 2^32
               e_hi = z_hi + d_hi + floor(e_lo / 2^32)
               e_lo = 0|((e_lo + 2^31) % 2^32 - 2^31)
               d_lo = c_lo;  d_hi = c_hi
               c_lo = b_lo;  c_hi = b_hi
               b_lo = a_lo;  b_hi = a_hi
               z_lo = z_lo + (d_lo & c_lo ~ b_lo & (d_lo ~ c_lo)) % 2^32 + (b_lo>>28 ~ b_hi<<4 ~ b_lo<<30 ~ b_hi>>2 ~ b_lo<<25 ~ b_hi>>7) % 2^32
               a_hi = z_hi + (d_hi & c_hi ~ b_hi & (d_hi ~ c_hi)) + (b_hi>>28 ~ b_lo<<4 ~ b_hi<<30 ~ b_lo>>2 ~ b_hi<<25 ~ b_lo>>7) + floor(z_lo / 2^32)
               a_lo = 0|((z_lo + 2^31) % 2^32 - 2^31)
            end
            a_lo = h1_lo % 2^32 + a_lo % 2^32
            h1_hi = h1_hi + a_hi + floor(a_lo / 2^32)
            h1_lo = 0|((a_lo + 2^31) % 2^32 - 2^31)
            a_lo = h2_lo % 2^32 + b_lo % 2^32
            h2_hi = h2_hi + b_hi + floor(a_lo / 2^32)
            h2_lo = 0|((a_lo + 2^31) % 2^32 - 2^31)
            a_lo = h3_lo % 2^32 + c_lo % 2^32
            h3_hi = h3_hi + c_hi + floor(a_lo / 2^32)
            h3_lo = 0|((a_lo + 2^31) % 2^32 - 2^31)
            a_lo = h4_lo % 2^32 + d_lo % 2^32
            h4_hi = h4_hi + d_hi + floor(a_lo / 2^32)
            h4_lo = 0|((a_lo + 2^31) % 2^32 - 2^31)
            a_lo = h5_lo % 2^32 + e_lo % 2^32
            h5_hi = h5_hi + e_hi + floor(a_lo / 2^32)
            h5_lo = 0|((a_lo + 2^31) % 2^32 - 2^31)
            a_lo = h6_lo % 2^32 + f_lo % 2^32
            h6_hi = h6_hi + f_hi + floor(a_lo / 2^32)
            h6_lo = 0|((a_lo + 2^31) % 2^32 - 2^31)
            a_lo = h7_lo % 2^32 + g_lo % 2^32
            h7_hi = h7_hi + g_hi + floor(a_lo / 2^32)
            h7_lo = 0|((a_lo + 2^31) % 2^32 - 2^31)
            a_lo = h8_lo % 2^32 + h_lo % 2^32
            h8_hi = h8_hi + h_hi + floor(a_lo / 2^32)
            h8_lo = 0|((a_lo + 2^31) % 2^32 - 2^31)
         end
         H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8] = h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo
         H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8] = h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi
      end

      local function md5_feed_64(H, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 64
         local W, K, md5_next_shift = common_W, md5_K, md5_next_shift
         local h1, h2, h3, h4 = H[1], H[2], H[3], H[4]
         for pos = offs + 1, offs + size, 64 do
            W[1], W[2], W[3], W[4], W[5], W[6], W[7], W[8], W[9], W[10], W[11], W[12], W[13], W[14], W[15], W[16] =
               string_unpack("<i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4", str, pos)
            local a, b, c, d = h1, h2, h3, h4
            local s = 32-7
            for j = 1, 16 do
               local F = (d ~ b & (c ~ d)) + a + K[j] + W[j]
               a = d
               d = c
               c = b
               b = (F << 32-s | F>>s) + b
               s = md5_next_shift[s]
            end
            s = 32-5
            for j = 17, 32 do
               local F = (c ~ d & (b ~ c)) + a + K[j] + W[(5*j-4 & 15) + 1]
               a = d
               d = c
               c = b
               b = (F << 32-s | F>>s) + b
               s = md5_next_shift[s]
            end
            s = 32-4
            for j = 33, 48 do
               local F = (b ~ c ~ d) + a + K[j] + W[(3*j+2 & 15) + 1]
               a = d
               d = c
               c = b
               b = (F << 32-s | F>>s) + b
               s = md5_next_shift[s]
            end
            s = 32-6
            for j = 49, 64 do
               local F = (c ~ (b | ~d)) + a + K[j] + W[(j*7-7 & 15) + 1]
               a = d
               d = c
               c = b
               b = (F << 32-s | F>>s) + b
               s = md5_next_shift[s]
            end
            h1 = a + h1
            h2 = b + h2
            h3 = c + h3
            h4 = d + h4
         end
         H[1], H[2], H[3], H[4] = h1, h2, h3, h4
      end

      local function sha1_feed_64(H, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 64
         local W = common_W
         local h1, h2, h3, h4, h5 = H[1], H[2], H[3], H[4], H[5]
         for pos = offs + 1, offs + size, 64 do
            W[1], W[2], W[3], W[4], W[5], W[6], W[7], W[8], W[9], W[10], W[11], W[12], W[13], W[14], W[15], W[16] =
               string_unpack(">i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4", str, pos)
            for j = 17, 80 do
               local a = W[j-3] ~ W[j-8] ~ W[j-14] ~ W[j-16]
               W[j] = a << 1 ~ a >> 31
            end
            local a, b, c, d, e = h1, h2, h3, h4, h5
            for j = 1, 20 do
               local z = (a << 5 ~ a >> 27) + (d ~ b & (c ~ d)) + 0x5A827999 + W[j] + e      -- constant = floor(2^30 * sqrt(2))
               e = d
               d = c
               c = b << 30 ~ b >> 2
               b = a
               a = z
            end
            for j = 21, 40 do
               local z = (a << 5 ~ a >> 27) + (b ~ c ~ d) + 0x6ED9EBA1 + W[j] + e            -- 2^30 * sqrt(3)
               e = d
               d = c
               c = b << 30 ~ b >> 2
               b = a
               a = z
            end
            for j = 41, 60 do
               local z = (a << 5 ~ a >> 27) + ((b ~ c) & d ~ b & c) + 0x8F1BBCDC + W[j] + e  -- 2^30 * sqrt(5)
               e = d
               d = c
               c = b << 30 ~ b >> 2
               b = a
               a = z
            end
            for j = 61, 80 do
               local z = (a << 5 ~ a >> 27) + (b ~ c ~ d) + 0xCA62C1D6 + W[j] + e            -- 2^30 * sqrt(10)
               e = d
               d = c
               c = b << 30 ~ b >> 2
               b = a
               a = z
            end
            h1 = a + h1
            h2 = b + h2
            h3 = c + h3
            h4 = d + h4
            h5 = e + h5
         end
         H[1], H[2], H[3], H[4], H[5] = h1, h2, h3, h4, h5
      end

      local keccak_format_i4i4 = build_keccak_format("i4i4")

      local function keccak_feed(lanes_lo, lanes_hi, str, offs, size, block_size_in_bytes)
         -- offs >= 0, size >= 0, size is multiple of block_size_in_bytes, block_size_in_bytes is positive multiple of 8
         local RC_lo, RC_hi = sha3_RC_lo, sha3_RC_hi
         local qwords_qty = block_size_in_bytes / 8
         local keccak_format = keccak_format_i4i4[qwords_qty]
         for pos = offs + 1, offs + size, block_size_in_bytes do
            local dwords_from_message = {string_unpack(keccak_format, str, pos)}
            for j = 1, qwords_qty do
               lanes_lo[j] = lanes_lo[j] ~ dwords_from_message[2*j-1]
               lanes_hi[j] = lanes_hi[j] ~ dwords_from_message[2*j]
            end
            local L01_lo, L01_hi, L02_lo, L02_hi, L03_lo, L03_hi, L04_lo, L04_hi, L05_lo, L05_hi, L06_lo, L06_hi, L07_lo, L07_hi, L08_lo, L08_hi,
               L09_lo, L09_hi, L10_lo, L10_hi, L11_lo, L11_hi, L12_lo, L12_hi, L13_lo, L13_hi, L14_lo, L14_hi, L15_lo, L15_hi, L16_lo, L16_hi,
               L17_lo, L17_hi, L18_lo, L18_hi, L19_lo, L19_hi, L20_lo, L20_hi, L21_lo, L21_hi, L22_lo, L22_hi, L23_lo, L23_hi, L24_lo, L24_hi, L25_lo, L25_hi =
               lanes_lo[1], lanes_hi[1], lanes_lo[2], lanes_hi[2], lanes_lo[3], lanes_hi[3], lanes_lo[4], lanes_hi[4], lanes_lo[5], lanes_hi[5],
               lanes_lo[6], lanes_hi[6], lanes_lo[7], lanes_hi[7], lanes_lo[8], lanes_hi[8], lanes_lo[9], lanes_hi[9], lanes_lo[10], lanes_hi[10],
               lanes_lo[11], lanes_hi[11], lanes_lo[12], lanes_hi[12], lanes_lo[13], lanes_hi[13], lanes_lo[14], lanes_hi[14], lanes_lo[15], lanes_hi[15],
               lanes_lo[16], lanes_hi[16], lanes_lo[17], lanes_hi[17], lanes_lo[18], lanes_hi[18], lanes_lo[19], lanes_hi[19], lanes_lo[20], lanes_hi[20],
               lanes_lo[21], lanes_hi[21], lanes_lo[22], lanes_hi[22], lanes_lo[23], lanes_hi[23], lanes_lo[24], lanes_hi[24], lanes_lo[25], lanes_hi[25]
            for round_idx = 1, 24 do
               local C1_lo = L01_lo ~ L06_lo ~ L11_lo ~ L16_lo ~ L21_lo
               local C1_hi = L01_hi ~ L06_hi ~ L11_hi ~ L16_hi ~ L21_hi
               local C2_lo = L02_lo ~ L07_lo ~ L12_lo ~ L17_lo ~ L22_lo
               local C2_hi = L02_hi ~ L07_hi ~ L12_hi ~ L17_hi ~ L22_hi
               local C3_lo = L03_lo ~ L08_lo ~ L13_lo ~ L18_lo ~ L23_lo
               local C3_hi = L03_hi ~ L08_hi ~ L13_hi ~ L18_hi ~ L23_hi
               local C4_lo = L04_lo ~ L09_lo ~ L14_lo ~ L19_lo ~ L24_lo
               local C4_hi = L04_hi ~ L09_hi ~ L14_hi ~ L19_hi ~ L24_hi
               local C5_lo = L05_lo ~ L10_lo ~ L15_lo ~ L20_lo ~ L25_lo
               local C5_hi = L05_hi ~ L10_hi ~ L15_hi ~ L20_hi ~ L25_hi
               local D_lo = C1_lo ~ C3_lo<<1 ~ C3_hi>>31
               local D_hi = C1_hi ~ C3_hi<<1 ~ C3_lo>>31
               local T0_lo = D_lo ~ L02_lo
               local T0_hi = D_hi ~ L02_hi
               local T1_lo = D_lo ~ L07_lo
               local T1_hi = D_hi ~ L07_hi
               local T2_lo = D_lo ~ L12_lo
               local T2_hi = D_hi ~ L12_hi
               local T3_lo = D_lo ~ L17_lo
               local T3_hi = D_hi ~ L17_hi
               local T4_lo = D_lo ~ L22_lo
               local T4_hi = D_hi ~ L22_hi
               L02_lo = T1_lo>>20 ~ T1_hi<<12
               L02_hi = T1_hi>>20 ~ T1_lo<<12
               L07_lo = T3_lo>>19 ~ T3_hi<<13
               L07_hi = T3_hi>>19 ~ T3_lo<<13
               L12_lo = T0_lo<<1 ~ T0_hi>>31
               L12_hi = T0_hi<<1 ~ T0_lo>>31
               L17_lo = T2_lo<<10 ~ T2_hi>>22
               L17_hi = T2_hi<<10 ~ T2_lo>>22
               L22_lo = T4_lo<<2 ~ T4_hi>>30
               L22_hi = T4_hi<<2 ~ T4_lo>>30
               D_lo = C2_lo ~ C4_lo<<1 ~ C4_hi>>31
               D_hi = C2_hi ~ C4_hi<<1 ~ C4_lo>>31
               T0_lo = D_lo ~ L03_lo
               T0_hi = D_hi ~ L03_hi
               T1_lo = D_lo ~ L08_lo
               T1_hi = D_hi ~ L08_hi
               T2_lo = D_lo ~ L13_lo
               T2_hi = D_hi ~ L13_hi
               T3_lo = D_lo ~ L18_lo
               T3_hi = D_hi ~ L18_hi
               T4_lo = D_lo ~ L23_lo
               T4_hi = D_hi ~ L23_hi
               L03_lo = T2_lo>>21 ~ T2_hi<<11
               L03_hi = T2_hi>>21 ~ T2_lo<<11
               L08_lo = T4_lo>>3 ~ T4_hi<<29
               L08_hi = T4_hi>>3 ~ T4_lo<<29
               L13_lo = T1_lo<<6 ~ T1_hi>>26
               L13_hi = T1_hi<<6 ~ T1_lo>>26
               L18_lo = T3_lo<<15 ~ T3_hi>>17
               L18_hi = T3_hi<<15 ~ T3_lo>>17
               L23_lo = T0_lo>>2 ~ T0_hi<<30
               L23_hi = T0_hi>>2 ~ T0_lo<<30
               D_lo = C3_lo ~ C5_lo<<1 ~ C5_hi>>31
               D_hi = C3_hi ~ C5_hi<<1 ~ C5_lo>>31
               T0_lo = D_lo ~ L04_lo
               T0_hi = D_hi ~ L04_hi
               T1_lo = D_lo ~ L09_lo
               T1_hi = D_hi ~ L09_hi
               T2_lo = D_lo ~ L14_lo
               T2_hi = D_hi ~ L14_hi
               T3_lo = D_lo ~ L19_lo
               T3_hi = D_hi ~ L19_hi
               T4_lo = D_lo ~ L24_lo
               T4_hi = D_hi ~ L24_hi
               L04_lo = T3_lo<<21 ~ T3_hi>>11
               L04_hi = T3_hi<<21 ~ T3_lo>>11
               L09_lo = T0_lo<<28 ~ T0_hi>>4
               L09_hi = T0_hi<<28 ~ T0_lo>>4
               L14_lo = T2_lo<<25 ~ T2_hi>>7
               L14_hi = T2_hi<<25 ~ T2_lo>>7
               L19_lo = T4_lo>>8 ~ T4_hi<<24
               L19_hi = T4_hi>>8 ~ T4_lo<<24
               L24_lo = T1_lo>>9 ~ T1_hi<<23
               L24_hi = T1_hi>>9 ~ T1_lo<<23
               D_lo = C4_lo ~ C1_lo<<1 ~ C1_hi>>31
               D_hi = C4_hi ~ C1_hi<<1 ~ C1_lo>>31
               T0_lo = D_lo ~ L05_lo
               T0_hi = D_hi ~ L05_hi
               T1_lo = D_lo ~ L10_lo
               T1_hi = D_hi ~ L10_hi
               T2_lo = D_lo ~ L15_lo
               T2_hi = D_hi ~ L15_hi
               T3_lo = D_lo ~ L20_lo
               T3_hi = D_hi ~ L20_hi
               T4_lo = D_lo ~ L25_lo
               T4_hi = D_hi ~ L25_hi
               L05_lo = T4_lo<<14 ~ T4_hi>>18
               L05_hi = T4_hi<<14 ~ T4_lo>>18
               L10_lo = T1_lo<<20 ~ T1_hi>>12
               L10_hi = T1_hi<<20 ~ T1_lo>>12
               L15_lo = T3_lo<<8 ~ T3_hi>>24
               L15_hi = T3_hi<<8 ~ T3_lo>>24
               L20_lo = T0_lo<<27 ~ T0_hi>>5
               L20_hi = T0_hi<<27 ~ T0_lo>>5
               L25_lo = T2_lo>>25 ~ T2_hi<<7
               L25_hi = T2_hi>>25 ~ T2_lo<<7
               D_lo = C5_lo ~ C2_lo<<1 ~ C2_hi>>31
               D_hi = C5_hi ~ C2_hi<<1 ~ C2_lo>>31
               T1_lo = D_lo ~ L06_lo
               T1_hi = D_hi ~ L06_hi
               T2_lo = D_lo ~ L11_lo
               T2_hi = D_hi ~ L11_hi
               T3_lo = D_lo ~ L16_lo
               T3_hi = D_hi ~ L16_hi
               T4_lo = D_lo ~ L21_lo
               T4_hi = D_hi ~ L21_hi
               L06_lo = T2_lo<<3 ~ T2_hi>>29
               L06_hi = T2_hi<<3 ~ T2_lo>>29
               L11_lo = T4_lo<<18 ~ T4_hi>>14
               L11_hi = T4_hi<<18 ~ T4_lo>>14
               L16_lo = T1_lo>>28 ~ T1_hi<<4
               L16_hi = T1_hi>>28 ~ T1_lo<<4
               L21_lo = T3_lo>>23 ~ T3_hi<<9
               L21_hi = T3_hi>>23 ~ T3_lo<<9
               L01_lo = D_lo ~ L01_lo
               L01_hi = D_hi ~ L01_hi
               L01_lo, L02_lo, L03_lo, L04_lo, L05_lo = L01_lo ~ ~L02_lo & L03_lo, L02_lo ~ ~L03_lo & L04_lo, L03_lo ~ ~L04_lo & L05_lo, L04_lo ~ ~L05_lo & L01_lo, L05_lo ~ ~L01_lo & L02_lo
               L01_hi, L02_hi, L03_hi, L04_hi, L05_hi = L01_hi ~ ~L02_hi & L03_hi, L02_hi ~ ~L03_hi & L04_hi, L03_hi ~ ~L04_hi & L05_hi, L04_hi ~ ~L05_hi & L01_hi, L05_hi ~ ~L01_hi & L02_hi
               L06_lo, L07_lo, L08_lo, L09_lo, L10_lo = L09_lo ~ ~L10_lo & L06_lo, L10_lo ~ ~L06_lo & L07_lo, L06_lo ~ ~L07_lo & L08_lo, L07_lo ~ ~L08_lo & L09_lo, L08_lo ~ ~L09_lo & L10_lo
               L06_hi, L07_hi, L08_hi, L09_hi, L10_hi = L09_hi ~ ~L10_hi & L06_hi, L10_hi ~ ~L06_hi & L07_hi, L06_hi ~ ~L07_hi & L08_hi, L07_hi ~ ~L08_hi & L09_hi, L08_hi ~ ~L09_hi & L10_hi
               L11_lo, L12_lo, L13_lo, L14_lo, L15_lo = L12_lo ~ ~L13_lo & L14_lo, L13_lo ~ ~L14_lo & L15_lo, L14_lo ~ ~L15_lo & L11_lo, L15_lo ~ ~L11_lo & L12_lo, L11_lo ~ ~L12_lo & L13_lo
               L11_hi, L12_hi, L13_hi, L14_hi, L15_hi = L12_hi ~ ~L13_hi & L14_hi, L13_hi ~ ~L14_hi & L15_hi, L14_hi ~ ~L15_hi & L11_hi, L15_hi ~ ~L11_hi & L12_hi, L11_hi ~ ~L12_hi & L13_hi
               L16_lo, L17_lo, L18_lo, L19_lo, L20_lo = L20_lo ~ ~L16_lo & L17_lo, L16_lo ~ ~L17_lo & L18_lo, L17_lo ~ ~L18_lo & L19_lo, L18_lo ~ ~L19_lo & L20_lo, L19_lo ~ ~L20_lo & L16_lo
               L16_hi, L17_hi, L18_hi, L19_hi, L20_hi = L20_hi ~ ~L16_hi & L17_hi, L16_hi ~ ~L17_hi & L18_hi, L17_hi ~ ~L18_hi & L19_hi, L18_hi ~ ~L19_hi & L20_hi, L19_hi ~ ~L20_hi & L16_hi
               L21_lo, L22_lo, L23_lo, L24_lo, L25_lo = L23_lo ~ ~L24_lo & L25_lo, L24_lo ~ ~L25_lo & L21_lo, L25_lo ~ ~L21_lo & L22_lo, L21_lo ~ ~L22_lo & L23_lo, L22_lo ~ ~L23_lo & L24_lo
               L21_hi, L22_hi, L23_hi, L24_hi, L25_hi = L23_hi ~ ~L24_hi & L25_hi, L24_hi ~ ~L25_hi & L21_hi, L25_hi ~ ~L21_hi & L22_hi, L21_hi ~ ~L22_hi & L23_hi, L22_hi ~ ~L23_hi & L24_hi
               L01_lo = L01_lo ~ RC_lo[round_idx]
               L01_hi = L01_hi ~ RC_hi[round_idx]
            end
            lanes_lo[1]  = L01_lo;  lanes_hi[1]  = L01_hi
            lanes_lo[2]  = L02_lo;  lanes_hi[2]  = L02_hi
            lanes_lo[3]  = L03_lo;  lanes_hi[3]  = L03_hi
            lanes_lo[4]  = L04_lo;  lanes_hi[4]  = L04_hi
            lanes_lo[5]  = L05_lo;  lanes_hi[5]  = L05_hi
            lanes_lo[6]  = L06_lo;  lanes_hi[6]  = L06_hi
            lanes_lo[7]  = L07_lo;  lanes_hi[7]  = L07_hi
            lanes_lo[8]  = L08_lo;  lanes_hi[8]  = L08_hi
            lanes_lo[9]  = L09_lo;  lanes_hi[9]  = L09_hi
            lanes_lo[10] = L10_lo;  lanes_hi[10] = L10_hi
            lanes_lo[11] = L11_lo;  lanes_hi[11] = L11_hi
            lanes_lo[12] = L12_lo;  lanes_hi[12] = L12_hi
            lanes_lo[13] = L13_lo;  lanes_hi[13] = L13_hi
            lanes_lo[14] = L14_lo;  lanes_hi[14] = L14_hi
            lanes_lo[15] = L15_lo;  lanes_hi[15] = L15_hi
            lanes_lo[16] = L16_lo;  lanes_hi[16] = L16_hi
            lanes_lo[17] = L17_lo;  lanes_hi[17] = L17_hi
            lanes_lo[18] = L18_lo;  lanes_hi[18] = L18_hi
            lanes_lo[19] = L19_lo;  lanes_hi[19] = L19_hi
            lanes_lo[20] = L20_lo;  lanes_hi[20] = L20_hi
            lanes_lo[21] = L21_lo;  lanes_hi[21] = L21_hi
            lanes_lo[22] = L22_lo;  lanes_hi[22] = L22_hi
            lanes_lo[23] = L23_lo;  lanes_hi[23] = L23_hi
            lanes_lo[24] = L24_lo;  lanes_hi[24] = L24_hi
            lanes_lo[25] = L25_lo;  lanes_hi[25] = L25_hi
         end
      end

      local function blake2s_feed_64(H, str, offs, size, bytes_compressed, last_block_size, is_last_node)
         -- offs >= 0, size >= 0, size is multiple of 64
         local W = common_W
         local h1, h2, h3, h4, h5, h6, h7, h8 = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
         for pos = offs + 1, offs + size, 64 do
            if str then
               W[1], W[2], W[3], W[4], W[5], W[6], W[7], W[8], W[9], W[10], W[11], W[12], W[13], W[14], W[15], W[16] =
                  string_unpack("<i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4", str, pos)
            end
            local v0, v1, v2, v3, v4, v5, v6, v7 = h1, h2, h3, h4, h5, h6, h7, h8
            local v8, v9, vA, vB, vC, vD, vE, vF = sha2_H_hi[1], sha2_H_hi[2], sha2_H_hi[3], sha2_H_hi[4], sha2_H_hi[5], sha2_H_hi[6], sha2_H_hi[7], sha2_H_hi[8]
            bytes_compressed = bytes_compressed + (last_block_size or 64)
            local t0 = bytes_compressed % 2^32
            local t1 = (bytes_compressed - t0) / 2^32
            t0 = (t0 + 2^31) % 2^32 - 2^31  -- convert to int32 range (-2^31)..(2^31-1) to avoid "number has no integer representation" error while XORing
            vC = vC ~ t0  -- t0 = low_4_bytes(bytes_compressed)
            vD = vD ~ t1  -- t1 = high_4_bytes(bytes_compressed)
            if last_block_size then  -- flag f0
               vE = ~vE
            end
            if is_last_node then  -- flag f1
               vF = ~vF
            end
            for j = 1, 10 do
               local row = sigma[j]
               v0 = v0 + v4 + W[row[1]]
               vC = vC ~ v0
               vC = vC >> 16 | vC << 16
               v8 = v8 + vC
               v4 = v4 ~ v8
               v4 = v4 >> 12 | v4 << 20
               v0 = v0 + v4 + W[row[2]]
               vC = vC ~ v0
               vC = vC >> 8 | vC << 24
               v8 = v8 + vC
               v4 = v4 ~ v8
               v4 = v4 >> 7 | v4 << 25
               v1 = v1 + v5 + W[row[3]]
               vD = vD ~ v1
               vD = vD >> 16 | vD << 16
               v9 = v9 + vD
               v5 = v5 ~ v9
               v5 = v5 >> 12 | v5 << 20
               v1 = v1 + v5 + W[row[4]]
               vD = vD ~ v1
               vD = vD >> 8 | vD << 24
               v9 = v9 + vD
               v5 = v5 ~ v9
               v5 = v5 >> 7 | v5 << 25
               v2 = v2 + v6 + W[row[5]]
               vE = vE ~ v2
               vE = vE >> 16 | vE << 16
               vA = vA + vE
               v6 = v6 ~ vA
               v6 = v6 >> 12 | v6 << 20
               v2 = v2 + v6 + W[row[6]]
               vE = vE ~ v2
               vE = vE >> 8 | vE << 24
               vA = vA + vE
               v6 = v6 ~ vA
               v6 = v6 >> 7 | v6 << 25
               v3 = v3 + v7 + W[row[7]]
               vF = vF ~ v3
               vF = vF >> 16 | vF << 16
               vB = vB + vF
               v7 = v7 ~ vB
               v7 = v7 >> 12 | v7 << 20
               v3 = v3 + v7 + W[row[8]]
               vF = vF ~ v3
               vF = vF >> 8 | vF << 24
               vB = vB + vF
               v7 = v7 ~ vB
               v7 = v7 >> 7 | v7 << 25
               v0 = v0 + v5 + W[row[9]]
               vF = vF ~ v0
               vF = vF >> 16 | vF << 16
               vA = vA + vF
               v5 = v5 ~ vA
               v5 = v5 >> 12 | v5 << 20
               v0 = v0 + v5 + W[row[10]]
               vF = vF ~ v0
               vF = vF >> 8 | vF << 24
               vA = vA + vF
               v5 = v5 ~ vA
               v5 = v5 >> 7 | v5 << 25
               v1 = v1 + v6 + W[row[11]]
               vC = vC ~ v1
               vC = vC >> 16 | vC << 16
               vB = vB + vC
               v6 = v6 ~ vB
               v6 = v6 >> 12 | v6 << 20
               v1 = v1 + v6 + W[row[12]]
               vC = vC ~ v1
               vC = vC >> 8 | vC << 24
               vB = vB + vC
               v6 = v6 ~ vB
               v6 = v6 >> 7 | v6 << 25
               v2 = v2 + v7 + W[row[13]]
               vD = vD ~ v2
               vD = vD >> 16 | vD << 16
               v8 = v8 + vD
               v7 = v7 ~ v8
               v7 = v7 >> 12 | v7 << 20
               v2 = v2 + v7 + W[row[14]]
               vD = vD ~ v2
               vD = vD >> 8 | vD << 24
               v8 = v8 + vD
               v7 = v7 ~ v8
               v7 = v7 >> 7 | v7 << 25
               v3 = v3 + v4 + W[row[15]]
               vE = vE ~ v3
               vE = vE >> 16 | vE << 16
               v9 = v9 + vE
               v4 = v4 ~ v9
               v4 = v4 >> 12 | v4 << 20
               v3 = v3 + v4 + W[row[16]]
               vE = vE ~ v3
               vE = vE >> 8 | vE << 24
               v9 = v9 + vE
               v4 = v4 ~ v9
               v4 = v4 >> 7 | v4 << 25
            end
            h1 = h1 ~ v0 ~ v8
            h2 = h2 ~ v1 ~ v9
            h3 = h3 ~ v2 ~ vA
            h4 = h4 ~ v3 ~ vB
            h5 = h5 ~ v4 ~ vC
            h6 = h6 ~ v5 ~ vD
            h7 = h7 ~ v6 ~ vE
            h8 = h8 ~ v7 ~ vF
         end
         H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8] = h1, h2, h3, h4, h5, h6, h7, h8
         return bytes_compressed
      end

      local function blake2b_feed_128(H_lo, H_hi, str, offs, size, bytes_compressed, last_block_size, is_last_node)
         -- offs >= 0, size >= 0, size is multiple of 128
         local W = common_W
         local h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo = H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8]
         local h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi = H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8]
         for pos = offs + 1, offs + size, 128 do
            if str then
               W[1], W[2], W[3], W[4], W[5], W[6], W[7], W[8], W[9], W[10], W[11], W[12], W[13], W[14], W[15], W[16],
               W[17], W[18], W[19], W[20], W[21], W[22], W[23], W[24], W[25], W[26], W[27], W[28], W[29], W[30], W[31], W[32] =
                  string_unpack("<i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4", str, pos)
            end
            local v0_lo, v1_lo, v2_lo, v3_lo, v4_lo, v5_lo, v6_lo, v7_lo = h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo
            local v0_hi, v1_hi, v2_hi, v3_hi, v4_hi, v5_hi, v6_hi, v7_hi = h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi
            local v8_lo, v9_lo, vA_lo, vB_lo, vC_lo, vD_lo, vE_lo, vF_lo = sha2_H_lo[1], sha2_H_lo[2], sha2_H_lo[3], sha2_H_lo[4], sha2_H_lo[5], sha2_H_lo[6], sha2_H_lo[7], sha2_H_lo[8]
            local v8_hi, v9_hi, vA_hi, vB_hi, vC_hi, vD_hi, vE_hi, vF_hi = sha2_H_hi[1], sha2_H_hi[2], sha2_H_hi[3], sha2_H_hi[4], sha2_H_hi[5], sha2_H_hi[6], sha2_H_hi[7], sha2_H_hi[8]
            bytes_compressed = bytes_compressed + (last_block_size or 128)
            local t0_lo = bytes_compressed % 2^32
            local t0_hi = (bytes_compressed - t0_lo) / 2^32
            t0_lo = (t0_lo + 2^31) % 2^32 - 2^31  -- convert to int32 range (-2^31)..(2^31-1) to avoid "number has no integer representation" error while XORing
            vC_lo = vC_lo ~ t0_lo  -- t0 = low_8_bytes(bytes_compressed)
            vC_hi = vC_hi ~ t0_hi
            -- t1 = high_8_bytes(bytes_compressed) = 0,  message length is always below 2^53 bytes
            if last_block_size then  -- flag f0
               vE_lo = ~vE_lo
               vE_hi = ~vE_hi
            end
            if is_last_node then  -- flag f1
               vF_lo = ~vF_lo
               vF_hi = ~vF_hi
            end
            for j = 1, 12 do
               local row = sigma[j]
               local k = row[1] * 2
               v0_lo = v0_lo % 2^32 + v4_lo % 2^32 + W[k-1] % 2^32
               v0_hi = v0_hi + v4_hi + floor(v0_lo / 2^32) + W[k]
               v0_lo = 0|((v0_lo + 2^31) % 2^32 - 2^31)
               vC_lo, vC_hi = vC_hi ~ v0_hi, vC_lo ~ v0_lo
               v8_lo = v8_lo % 2^32 + vC_lo % 2^32
               v8_hi = v8_hi + vC_hi + floor(v8_lo / 2^32)
               v8_lo = 0|((v8_lo + 2^31) % 2^32 - 2^31)
               v4_lo, v4_hi = v4_lo ~ v8_lo, v4_hi ~ v8_hi
               v4_lo, v4_hi = v4_lo >> 24 | v4_hi << 8, v4_hi >> 24 | v4_lo << 8
               k = row[2] * 2
               v0_lo = v0_lo % 2^32 + v4_lo % 2^32 + W[k-1] % 2^32
               v0_hi = v0_hi + v4_hi + floor(v0_lo / 2^32) + W[k]
               v0_lo = 0|((v0_lo + 2^31) % 2^32 - 2^31)
               vC_lo, vC_hi = vC_lo ~ v0_lo, vC_hi ~ v0_hi
               vC_lo, vC_hi = vC_lo >> 16 | vC_hi << 16, vC_hi >> 16 | vC_lo << 16
               v8_lo = v8_lo % 2^32 + vC_lo % 2^32
               v8_hi = v8_hi + vC_hi + floor(v8_lo / 2^32)
               v8_lo = 0|((v8_lo + 2^31) % 2^32 - 2^31)
               v4_lo, v4_hi = v4_lo ~ v8_lo, v4_hi ~ v8_hi
               v4_lo, v4_hi = v4_lo << 1 | v4_hi >> 31, v4_hi << 1 | v4_lo >> 31
               k = row[3] * 2
               v1_lo = v1_lo % 2^32 + v5_lo % 2^32 + W[k-1] % 2^32
               v1_hi = v1_hi + v5_hi + floor(v1_lo / 2^32) + W[k]
               v1_lo = 0|((v1_lo + 2^31) % 2^32 - 2^31)
               vD_lo, vD_hi = vD_hi ~ v1_hi, vD_lo ~ v1_lo
               v9_lo = v9_lo % 2^32 + vD_lo % 2^32
               v9_hi = v9_hi + vD_hi + floor(v9_lo / 2^32)
               v9_lo = 0|((v9_lo + 2^31) % 2^32 - 2^31)
               v5_lo, v5_hi = v5_lo ~ v9_lo, v5_hi ~ v9_hi
               v5_lo, v5_hi = v5_lo >> 24 | v5_hi << 8, v5_hi >> 24 | v5_lo << 8
               k = row[4] * 2
               v1_lo = v1_lo % 2^32 + v5_lo % 2^32 + W[k-1] % 2^32
               v1_hi = v1_hi + v5_hi + floor(v1_lo / 2^32) + W[k]
               v1_lo = 0|((v1_lo + 2^31) % 2^32 - 2^31)
               vD_lo, vD_hi = vD_lo ~ v1_lo, vD_hi ~ v1_hi
               vD_lo, vD_hi = vD_lo >> 16 | vD_hi << 16, vD_hi >> 16 | vD_lo << 16
               v9_lo = v9_lo % 2^32 + vD_lo % 2^32
               v9_hi = v9_hi + vD_hi + floor(v9_lo / 2^32)
               v9_lo = 0|((v9_lo + 2^31) % 2^32 - 2^31)
               v5_lo, v5_hi = v5_lo ~ v9_lo, v5_hi ~ v9_hi
               v5_lo, v5_hi = v5_lo << 1 | v5_hi >> 31, v5_hi << 1 | v5_lo >> 31
               k = row[5] * 2
               v2_lo = v2_lo % 2^32 + v6_lo % 2^32 + W[k-1] % 2^32
               v2_hi = v2_hi + v6_hi + floor(v2_lo / 2^32) + W[k]
               v2_lo = 0|((v2_lo + 2^31) % 2^32 - 2^31)
               vE_lo, vE_hi = vE_hi ~ v2_hi, vE_lo ~ v2_lo
               vA_lo = vA_lo % 2^32 + vE_lo % 2^32
               vA_hi = vA_hi + vE_hi + floor(vA_lo / 2^32)
               vA_lo = 0|((vA_lo + 2^31) % 2^32 - 2^31)
               v6_lo, v6_hi = v6_lo ~ vA_lo, v6_hi ~ vA_hi
               v6_lo, v6_hi = v6_lo >> 24 | v6_hi << 8, v6_hi >> 24 | v6_lo << 8
               k = row[6] * 2
               v2_lo = v2_lo % 2^32 + v6_lo % 2^32 + W[k-1] % 2^32
               v2_hi = v2_hi + v6_hi + floor(v2_lo / 2^32) + W[k]
               v2_lo = 0|((v2_lo + 2^31) % 2^32 - 2^31)
               vE_lo, vE_hi = vE_lo ~ v2_lo, vE_hi ~ v2_hi
               vE_lo, vE_hi = vE_lo >> 16 | vE_hi << 16, vE_hi >> 16 | vE_lo << 16
               vA_lo = vA_lo % 2^32 + vE_lo % 2^32
               vA_hi = vA_hi + vE_hi + floor(vA_lo / 2^32)
               vA_lo = 0|((vA_lo + 2^31) % 2^32 - 2^31)
               v6_lo, v6_hi = v6_lo ~ vA_lo, v6_hi ~ vA_hi
               v6_lo, v6_hi = v6_lo << 1 | v6_hi >> 31, v6_hi << 1 | v6_lo >> 31
               k = row[7] * 2
               v3_lo = v3_lo % 2^32 + v7_lo % 2^32 + W[k-1] % 2^32
               v3_hi = v3_hi + v7_hi + floor(v3_lo / 2^32) + W[k]
               v3_lo = 0|((v3_lo + 2^31) % 2^32 - 2^31)
               vF_lo, vF_hi = vF_hi ~ v3_hi, vF_lo ~ v3_lo
               vB_lo = vB_lo % 2^32 + vF_lo % 2^32
               vB_hi = vB_hi + vF_hi + floor(vB_lo / 2^32)
               vB_lo = 0|((vB_lo + 2^31) % 2^32 - 2^31)
               v7_lo, v7_hi = v7_lo ~ vB_lo, v7_hi ~ vB_hi
               v7_lo, v7_hi = v7_lo >> 24 | v7_hi << 8, v7_hi >> 24 | v7_lo << 8
               k = row[8] * 2
               v3_lo = v3_lo % 2^32 + v7_lo % 2^32 + W[k-1] % 2^32
               v3_hi = v3_hi + v7_hi + floor(v3_lo / 2^32) + W[k]
               v3_lo = 0|((v3_lo + 2^31) % 2^32 - 2^31)
               vF_lo, vF_hi = vF_lo ~ v3_lo, vF_hi ~ v3_hi
               vF_lo, vF_hi = vF_lo >> 16 | vF_hi << 16, vF_hi >> 16 | vF_lo << 16
               vB_lo = vB_lo % 2^32 + vF_lo % 2^32
               vB_hi = vB_hi + vF_hi + floor(vB_lo / 2^32)
               vB_lo = 0|((vB_lo + 2^31) % 2^32 - 2^31)
               v7_lo, v7_hi = v7_lo ~ vB_lo, v7_hi ~ vB_hi
               v7_lo, v7_hi = v7_lo << 1 | v7_hi >> 31, v7_hi << 1 | v7_lo >> 31
               k = row[9] * 2
               v0_lo = v0_lo % 2^32 + v5_lo % 2^32 + W[k-1] % 2^32
               v0_hi = v0_hi + v5_hi + floor(v0_lo / 2^32) + W[k]
               v0_lo = 0|((v0_lo + 2^31) % 2^32 - 2^31)
               vF_lo, vF_hi = vF_hi ~ v0_hi, vF_lo ~ v0_lo
               vA_lo = vA_lo % 2^32 + vF_lo % 2^32
               vA_hi = vA_hi + vF_hi + floor(vA_lo / 2^32)
               vA_lo = 0|((vA_lo + 2^31) % 2^32 - 2^31)
               v5_lo, v5_hi = v5_lo ~ vA_lo, v5_hi ~ vA_hi
               v5_lo, v5_hi = v5_lo >> 24 | v5_hi << 8, v5_hi >> 24 | v5_lo << 8
               k = row[10] * 2
               v0_lo = v0_lo % 2^32 + v5_lo % 2^32 + W[k-1] % 2^32
               v0_hi = v0_hi + v5_hi + floor(v0_lo / 2^32) + W[k]
               v0_lo = 0|((v0_lo + 2^31) % 2^32 - 2^31)
               vF_lo, vF_hi = vF_lo ~ v0_lo, vF_hi ~ v0_hi
               vF_lo, vF_hi = vF_lo >> 16 | vF_hi << 16, vF_hi >> 16 | vF_lo << 16
               vA_lo = vA_lo % 2^32 + vF_lo % 2^32
               vA_hi = vA_hi + vF_hi + floor(vA_lo / 2^32)
               vA_lo = 0|((vA_lo + 2^31) % 2^32 - 2^31)
               v5_lo, v5_hi = v5_lo ~ vA_lo, v5_hi ~ vA_hi
               v5_lo, v5_hi = v5_lo << 1 | v5_hi >> 31, v5_hi << 1 | v5_lo >> 31
               k = row[11] * 2
               v1_lo = v1_lo % 2^32 + v6_lo % 2^32 + W[k-1] % 2^32
               v1_hi = v1_hi + v6_hi + floor(v1_lo / 2^32) + W[k]
               v1_lo = 0|((v1_lo + 2^31) % 2^32 - 2^31)
               vC_lo, vC_hi = vC_hi ~ v1_hi, vC_lo ~ v1_lo
               vB_lo = vB_lo % 2^32 + vC_lo % 2^32
               vB_hi = vB_hi + vC_hi + floor(vB_lo / 2^32)
               vB_lo = 0|((vB_lo + 2^31) % 2^32 - 2^31)
               v6_lo, v6_hi = v6_lo ~ vB_lo, v6_hi ~ vB_hi
               v6_lo, v6_hi = v6_lo >> 24 | v6_hi << 8, v6_hi >> 24 | v6_lo << 8
               k = row[12] * 2
               v1_lo = v1_lo % 2^32 + v6_lo % 2^32 + W[k-1] % 2^32
               v1_hi = v1_hi + v6_hi + floor(v1_lo / 2^32) + W[k]
               v1_lo = 0|((v1_lo + 2^31) % 2^32 - 2^31)
               vC_lo, vC_hi = vC_lo ~ v1_lo, vC_hi ~ v1_hi
               vC_lo, vC_hi = vC_lo >> 16 | vC_hi << 16, vC_hi >> 16 | vC_lo << 16
               vB_lo = vB_lo % 2^32 + vC_lo % 2^32
               vB_hi = vB_hi + vC_hi + floor(vB_lo / 2^32)
               vB_lo = 0|((vB_lo + 2^31) % 2^32 - 2^31)
               v6_lo, v6_hi = v6_lo ~ vB_lo, v6_hi ~ vB_hi
               v6_lo, v6_hi = v6_lo << 1 | v6_hi >> 31, v6_hi << 1 | v6_lo >> 31
               k = row[13] * 2
               v2_lo = v2_lo % 2^32 + v7_lo % 2^32 + W[k-1] % 2^32
               v2_hi = v2_hi + v7_hi + floor(v2_lo / 2^32) + W[k]
               v2_lo = 0|((v2_lo + 2^31) % 2^32 - 2^31)
               vD_lo, vD_hi = vD_hi ~ v2_hi, vD_lo ~ v2_lo
               v8_lo = v8_lo % 2^32 + vD_lo % 2^32
               v8_hi = v8_hi + vD_hi + floor(v8_lo / 2^32)
               v8_lo = 0|((v8_lo + 2^31) % 2^32 - 2^31)
               v7_lo, v7_hi = v7_lo ~ v8_lo, v7_hi ~ v8_hi
               v7_lo, v7_hi = v7_lo >> 24 | v7_hi << 8, v7_hi >> 24 | v7_lo << 8
               k = row[14] * 2
               v2_lo = v2_lo % 2^32 + v7_lo % 2^32 + W[k-1] % 2^32
               v2_hi = v2_hi + v7_hi + floor(v2_lo / 2^32) + W[k]
               v2_lo = 0|((v2_lo + 2^31) % 2^32 - 2^31)
               vD_lo, vD_hi = vD_lo ~ v2_lo, vD_hi ~ v2_hi
               vD_lo, vD_hi = vD_lo >> 16 | vD_hi << 16, vD_hi >> 16 | vD_lo << 16
               v8_lo = v8_lo % 2^32 + vD_lo % 2^32
               v8_hi = v8_hi + vD_hi + floor(v8_lo / 2^32)
               v8_lo = 0|((v8_lo + 2^31) % 2^32 - 2^31)
               v7_lo, v7_hi = v7_lo ~ v8_lo, v7_hi ~ v8_hi
               v7_lo, v7_hi = v7_lo << 1 | v7_hi >> 31, v7_hi << 1 | v7_lo >> 31
               k = row[15] * 2
               v3_lo = v3_lo % 2^32 + v4_lo % 2^32 + W[k-1] % 2^32
               v3_hi = v3_hi + v4_hi + floor(v3_lo / 2^32) + W[k]
               v3_lo = 0|((v3_lo + 2^31) % 2^32 - 2^31)
               vE_lo, vE_hi = vE_hi ~ v3_hi, vE_lo ~ v3_lo
               v9_lo = v9_lo % 2^32 + vE_lo % 2^32
               v9_hi = v9_hi + vE_hi + floor(v9_lo / 2^32)
               v9_lo = 0|((v9_lo + 2^31) % 2^32 - 2^31)
               v4_lo, v4_hi = v4_lo ~ v9_lo, v4_hi ~ v9_hi
               v4_lo, v4_hi = v4_lo >> 24 | v4_hi << 8, v4_hi >> 24 | v4_lo << 8
               k = row[16] * 2
               v3_lo = v3_lo % 2^32 + v4_lo % 2^32 + W[k-1] % 2^32
               v3_hi = v3_hi + v4_hi + floor(v3_lo / 2^32) + W[k]
               v3_lo = 0|((v3_lo + 2^31) % 2^32 - 2^31)
               vE_lo, vE_hi = vE_lo ~ v3_lo, vE_hi ~ v3_hi
               vE_lo, vE_hi = vE_lo >> 16 | vE_hi << 16, vE_hi >> 16 | vE_lo << 16
               v9_lo = v9_lo % 2^32 + vE_lo % 2^32
               v9_hi = v9_hi + vE_hi + floor(v9_lo / 2^32)
               v9_lo = 0|((v9_lo + 2^31) % 2^32 - 2^31)
               v4_lo, v4_hi = v4_lo ~ v9_lo, v4_hi ~ v9_hi
               v4_lo, v4_hi = v4_lo << 1 | v4_hi >> 31, v4_hi << 1 | v4_lo >> 31
            end
            h1_lo = h1_lo ~ v0_lo ~ v8_lo
            h2_lo = h2_lo ~ v1_lo ~ v9_lo
            h3_lo = h3_lo ~ v2_lo ~ vA_lo
            h4_lo = h4_lo ~ v3_lo ~ vB_lo
            h5_lo = h5_lo ~ v4_lo ~ vC_lo
            h6_lo = h6_lo ~ v5_lo ~ vD_lo
            h7_lo = h7_lo ~ v6_lo ~ vE_lo
            h8_lo = h8_lo ~ v7_lo ~ vF_lo
            h1_hi = h1_hi ~ v0_hi ~ v8_hi
            h2_hi = h2_hi ~ v1_hi ~ v9_hi
            h3_hi = h3_hi ~ v2_hi ~ vA_hi
            h4_hi = h4_hi ~ v3_hi ~ vB_hi
            h5_hi = h5_hi ~ v4_hi ~ vC_hi
            h6_hi = h6_hi ~ v5_hi ~ vD_hi
            h7_hi = h7_hi ~ v6_hi ~ vE_hi
            h8_hi = h8_hi ~ v7_hi ~ vF_hi
         end
         H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8] = h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo
         H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8] = h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi
         return bytes_compressed
      end

      local function blake3_feed_64(str, offs, size, flags, chunk_index, H_in, H_out, wide_output, block_length)
         -- offs >= 0, size >= 0, size is multiple of 64
         block_length = block_length or 64
         local W = common_W
         local h1, h2, h3, h4, h5, h6, h7, h8 = H_in[1], H_in[2], H_in[3], H_in[4], H_in[5], H_in[6], H_in[7], H_in[8]
         H_out = H_out or H_in
         for pos = offs + 1, offs + size, 64 do
            if str then
               W[1], W[2], W[3], W[4], W[5], W[6], W[7], W[8], W[9], W[10], W[11], W[12], W[13], W[14], W[15], W[16] =
                  string_unpack("<i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4", str, pos)
            end
            local v0, v1, v2, v3, v4, v5, v6, v7 = h1, h2, h3, h4, h5, h6, h7, h8
            local v8, v9, vA, vB = sha2_H_hi[1], sha2_H_hi[2], sha2_H_hi[3], sha2_H_hi[4]
            local t0 = chunk_index % 2^32         -- t0 = low_4_bytes(chunk_index)
            local t1 = (chunk_index - t0) / 2^32  -- t1 = high_4_bytes(chunk_index)
            t0 = (t0 + 2^31) % 2^32 - 2^31  -- convert to int32 range (-2^31)..(2^31-1) to avoid "number has no integer representation" error while ORing
            local vC, vD, vE, vF = 0|t0, 0|t1, block_length, flags
            for j = 1, 7 do
               v0 = v0 + v4 + W[perm_blake3[j]]
               vC = vC ~ v0
               vC = vC >> 16 | vC << 16
               v8 = v8 + vC
               v4 = v4 ~ v8
               v4 = v4 >> 12 | v4 << 20
               v0 = v0 + v4 + W[perm_blake3[j + 14]]
               vC = vC ~ v0
               vC = vC >> 8 | vC << 24
               v8 = v8 + vC
               v4 = v4 ~ v8
               v4 = v4 >> 7 | v4 << 25
               v1 = v1 + v5 + W[perm_blake3[j + 1]]
               vD = vD ~ v1
               vD = vD >> 16 | vD << 16
               v9 = v9 + vD
               v5 = v5 ~ v9
               v5 = v5 >> 12 | v5 << 20
               v1 = v1 + v5 + W[perm_blake3[j + 2]]
               vD = vD ~ v1
               vD = vD >> 8 | vD << 24
               v9 = v9 + vD
               v5 = v5 ~ v9
               v5 = v5 >> 7 | v5 << 25
               v2 = v2 + v6 + W[perm_blake3[j + 16]]
               vE = vE ~ v2
               vE = vE >> 16 | vE << 16
               vA = vA + vE
               v6 = v6 ~ vA
               v6 = v6 >> 12 | v6 << 20
               v2 = v2 + v6 + W[perm_blake3[j + 7]]
               vE = vE ~ v2
               vE = vE >> 8 | vE << 24
               vA = vA + vE
               v6 = v6 ~ vA
               v6 = v6 >> 7 | v6 << 25
               v3 = v3 + v7 + W[perm_blake3[j + 15]]
               vF = vF ~ v3
               vF = vF >> 16 | vF << 16
               vB = vB + vF
               v7 = v7 ~ vB
               v7 = v7 >> 12 | v7 << 20
               v3 = v3 + v7 + W[perm_blake3[j + 17]]
               vF = vF ~ v3
               vF = vF >> 8 | vF << 24
               vB = vB + vF
               v7 = v7 ~ vB
               v7 = v7 >> 7 | v7 << 25
               v0 = v0 + v5 + W[perm_blake3[j + 21]]
               vF = vF ~ v0
               vF = vF >> 16 | vF << 16
               vA = vA + vF
               v5 = v5 ~ vA
               v5 = v5 >> 12 | v5 << 20
               v0 = v0 + v5 + W[perm_blake3[j + 5]]
               vF = vF ~ v0
               vF = vF >> 8 | vF << 24
               vA = vA + vF
               v5 = v5 ~ vA
               v5 = v5 >> 7 | v5 << 25
               v1 = v1 + v6 + W[perm_blake3[j + 3]]
               vC = vC ~ v1
               vC = vC >> 16 | vC << 16
               vB = vB + vC
               v6 = v6 ~ vB
               v6 = v6 >> 12 | v6 << 20
               v1 = v1 + v6 + W[perm_blake3[j + 6]]
               vC = vC ~ v1
               vC = vC >> 8 | vC << 24
               vB = vB + vC
               v6 = v6 ~ vB
               v6 = v6 >> 7 | v6 << 25
               v2 = v2 + v7 + W[perm_blake3[j + 4]]
               vD = vD ~ v2
               vD = vD >> 16 | vD << 16
               v8 = v8 + vD
               v7 = v7 ~ v8
               v7 = v7 >> 12 | v7 << 20
               v2 = v2 + v7 + W[perm_blake3[j + 18]]
               vD = vD ~ v2
               vD = vD >> 8 | vD << 24
               v8 = v8 + vD
               v7 = v7 ~ v8
               v7 = v7 >> 7 | v7 << 25
               v3 = v3 + v4 + W[perm_blake3[j + 19]]
               vE = vE ~ v3
               vE = vE >> 16 | vE << 16
               v9 = v9 + vE
               v4 = v4 ~ v9
               v4 = v4 >> 12 | v4 << 20
               v3 = v3 + v4 + W[perm_blake3[j + 20]]
               vE = vE ~ v3
               vE = vE >> 8 | vE << 24
               v9 = v9 + vE
               v4 = v4 ~ v9
               v4 = v4 >> 7 | v4 << 25
            end
            if wide_output then
               H_out[ 9] = h1 ~ v8
               H_out[10] = h2 ~ v9
               H_out[11] = h3 ~ vA
               H_out[12] = h4 ~ vB
               H_out[13] = h5 ~ vC
               H_out[14] = h6 ~ vD
               H_out[15] = h7 ~ vE
               H_out[16] = h8 ~ vF
            end
            h1 = v0 ~ v8
            h2 = v1 ~ v9
            h3 = v2 ~ vA
            h4 = v3 ~ vB
            h5 = v4 ~ vC
            h6 = v5 ~ vD
            h7 = v6 ~ vE
            h8 = v7 ~ vF
         end
         H_out[1], H_out[2], H_out[3], H_out[4], H_out[5], H_out[6], H_out[7], H_out[8] = h1, h2, h3, h4, h5, h6, h7, h8
      end

      return XORA5, XOR_BYTE, sha256_feed_64, sha512_feed_128, md5_feed_64, sha1_feed_64, keccak_feed, blake2s_feed_64, blake2b_feed_128, blake3_feed_64
   ]=](md5_next_shift, md5_K, sha2_K_lo, sha2_K_hi, build_keccak_format, sha3_RC_lo, sha3_RC_hi, sigma, common_W, sha2_H_lo, sha2_H_hi, perm_blake3)

end

XOR = XOR or XORA5

if branch == "LIB32" or branch == "EMUL" then


   -- implementation for Lua 5.1/5.2 (with or without bitwise library available)

   function sha256_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W, K = common_W, sha2_K_hi
      local h1, h2, h3, h4, h5, h6, h7, h8 = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
      for pos = offs, offs + size - 1, 64 do
         for j = 1, 16 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)
            W[j] = ((a * 256 + b) * 256 + c) * 256 + d
         end
         for j = 17, 64 do
            local a, b = W[j-15], W[j-2]
            local a7, a18, b17, b19 = a / 2^7, a / 2^18, b / 2^17, b / 2^19
            W[j] = (XOR(a7 % 1 * (2^32 - 1) + a7, a18 % 1 * (2^32 - 1) + a18, (a - a % 2^3) / 2^3) + W[j-16] + W[j-7]
               + XOR(b17 % 1 * (2^32 - 1) + b17, b19 % 1 * (2^32 - 1) + b19, (b - b % 2^10) / 2^10)) % 2^32
         end
         local a, b, c, d, e, f, g, h = h1, h2, h3, h4, h5, h6, h7, h8
         for j = 1, 64 do
            e = e % 2^32
            local e6, e11, e7 = e / 2^6, e / 2^11, e * 2^7
            local e7_lo = e7 % 2^32
            local z = AND(e, f) + AND(-1-e, g) + h + K[j] + W[j]
               + XOR(e6 % 1 * (2^32 - 1) + e6, e11 % 1 * (2^32 - 1) + e11, e7_lo + (e7 - e7_lo) / 2^32)
            h = g
            g = f
            f = e
            e = z + d
            d = c
            c = b
            b = a % 2^32
            local b2, b13, b10 = b / 2^2, b / 2^13, b * 2^10
            local b10_lo = b10 % 2^32
            a = z + AND(d, c) + AND(b, XOR(d, c)) +
               XOR(b2 % 1 * (2^32 - 1) + b2, b13 % 1 * (2^32 - 1) + b13, b10_lo + (b10 - b10_lo) / 2^32)
         end
         h1, h2, h3, h4 = (a + h1) % 2^32, (b + h2) % 2^32, (c + h3) % 2^32, (d + h4) % 2^32
         h5, h6, h7, h8 = (e + h5) % 2^32, (f + h6) % 2^32, (g + h7) % 2^32, (h + h8) % 2^32
      end
      H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8] = h1, h2, h3, h4, h5, h6, h7, h8
   end


   function sha512_feed_128(H_lo, H_hi, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 128
      -- W1_hi, W1_lo, W2_hi, W2_lo, ...   Wk_hi = W[2*k-1], Wk_lo = W[2*k]
      local W, K_lo, K_hi = common_W, sha2_K_lo, sha2_K_hi
      local h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo = H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8]
      local h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi = H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8]
      for pos = offs, offs + size - 1, 128 do
         for j = 1, 16*2 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)
            W[j] = ((a * 256 + b) * 256 + c) * 256 + d
         end
         for jj = 17*2, 80*2, 2 do
            local a_hi, a_lo, b_hi, b_lo = W[jj-31], W[jj-30], W[jj-5], W[jj-4]
            local b_hi_6, b_hi_19, b_hi_29, b_lo_19, b_lo_29, a_hi_1, a_hi_7, a_hi_8, a_lo_1, a_lo_8 =
               b_hi % 2^6, b_hi % 2^19, b_hi % 2^29, b_lo % 2^19, b_lo % 2^29, a_hi % 2^1, a_hi % 2^7, a_hi % 2^8, a_lo % 2^1, a_lo % 2^8
            local tmp1 = XOR((a_lo - a_lo_1) / 2^1 + a_hi_1 * 2^31, (a_lo - a_lo_8) / 2^8 + a_hi_8 * 2^24, (a_lo - a_lo % 2^7) / 2^7 + a_hi_7 * 2^25) % 2^32
               + XOR((b_lo - b_lo_19) / 2^19 + b_hi_19 * 2^13, b_lo_29 * 2^3 + (b_hi - b_hi_29) / 2^29, (b_lo - b_lo % 2^6) / 2^6 + b_hi_6 * 2^26) % 2^32
               + W[jj-14] + W[jj-32]
            local tmp2 = tmp1 % 2^32
            W[jj-1] = (XOR((a_hi - a_hi_1) / 2^1 + a_lo_1 * 2^31, (a_hi - a_hi_8) / 2^8 + a_lo_8 * 2^24, (a_hi - a_hi_7) / 2^7)
               + XOR((b_hi - b_hi_19) / 2^19 + b_lo_19 * 2^13, b_hi_29 * 2^3 + (b_lo - b_lo_29) / 2^29, (b_hi - b_hi_6) / 2^6)
               + W[jj-15] + W[jj-33] + (tmp1 - tmp2) / 2^32) % 2^32
            W[jj] = tmp2
         end
         local a_lo, b_lo, c_lo, d_lo, e_lo, f_lo, g_lo, h_lo = h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo
         local a_hi, b_hi, c_hi, d_hi, e_hi, f_hi, g_hi, h_hi = h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi
         for j = 1, 80 do
            local jj = 2*j
            local e_lo_9, e_lo_14, e_lo_18, e_hi_9, e_hi_14, e_hi_18 = e_lo % 2^9, e_lo % 2^14, e_lo % 2^18, e_hi % 2^9, e_hi % 2^14, e_hi % 2^18
            local tmp1 = (AND(e_lo, f_lo) + AND(-1-e_lo, g_lo)) % 2^32 + h_lo + K_lo[j] + W[jj]
               + XOR((e_lo - e_lo_14) / 2^14 + e_hi_14 * 2^18, (e_lo - e_lo_18) / 2^18 + e_hi_18 * 2^14, e_lo_9 * 2^23 + (e_hi - e_hi_9) / 2^9) % 2^32
            local z_lo = tmp1 % 2^32
            local z_hi = AND(e_hi, f_hi) + AND(-1-e_hi, g_hi) + h_hi + K_hi[j] + W[jj-1] + (tmp1 - z_lo) / 2^32
               + XOR((e_hi - e_hi_14) / 2^14 + e_lo_14 * 2^18, (e_hi - e_hi_18) / 2^18 + e_lo_18 * 2^14, e_hi_9 * 2^23 + (e_lo - e_lo_9) / 2^9)
            h_lo = g_lo;  h_hi = g_hi
            g_lo = f_lo;  g_hi = f_hi
            f_lo = e_lo;  f_hi = e_hi
            tmp1 = z_lo + d_lo
            e_lo = tmp1 % 2^32
            e_hi = (z_hi + d_hi + (tmp1 - e_lo) / 2^32) % 2^32
            d_lo = c_lo;  d_hi = c_hi
            c_lo = b_lo;  c_hi = b_hi
            b_lo = a_lo;  b_hi = a_hi
            local b_lo_2, b_lo_7, b_lo_28, b_hi_2, b_hi_7, b_hi_28 = b_lo % 2^2, b_lo % 2^7, b_lo % 2^28, b_hi % 2^2, b_hi % 2^7, b_hi % 2^28
            tmp1 = z_lo + (AND(d_lo, c_lo) + AND(b_lo, XOR(d_lo, c_lo))) % 2^32
               + XOR((b_lo - b_lo_28) / 2^28 + b_hi_28 * 2^4, b_lo_2 * 2^30 + (b_hi - b_hi_2) / 2^2, b_lo_7 * 2^25 + (b_hi - b_hi_7) / 2^7) % 2^32
            a_lo = tmp1 % 2^32
            a_hi = (z_hi + AND(d_hi, c_hi) + AND(b_hi, XOR(d_hi, c_hi)) + (tmp1 - a_lo) / 2^32
               + XOR((b_hi - b_hi_28) / 2^28 + b_lo_28 * 2^4, b_hi_2 * 2^30 + (b_lo - b_lo_2) / 2^2, b_hi_7 * 2^25 + (b_lo - b_lo_7) / 2^7)) % 2^32
         end
         a_lo = h1_lo + a_lo
         h1_lo = a_lo % 2^32
         h1_hi = (h1_hi + a_hi + (a_lo - h1_lo) / 2^32) % 2^32
         a_lo = h2_lo + b_lo
         h2_lo = a_lo % 2^32
         h2_hi = (h2_hi + b_hi + (a_lo - h2_lo) / 2^32) % 2^32
         a_lo = h3_lo + c_lo
         h3_lo = a_lo % 2^32
         h3_hi = (h3_hi + c_hi + (a_lo - h3_lo) / 2^32) % 2^32
         a_lo = h4_lo + d_lo
         h4_lo = a_lo % 2^32
         h4_hi = (h4_hi + d_hi + (a_lo - h4_lo) / 2^32) % 2^32
         a_lo = h5_lo + e_lo
         h5_lo = a_lo % 2^32
         h5_hi = (h5_hi + e_hi + (a_lo - h5_lo) / 2^32) % 2^32
         a_lo = h6_lo + f_lo
         h6_lo = a_lo % 2^32
         h6_hi = (h6_hi + f_hi + (a_lo - h6_lo) / 2^32) % 2^32
         a_lo = h7_lo + g_lo
         h7_lo = a_lo % 2^32
         h7_hi = (h7_hi + g_hi + (a_lo - h7_lo) / 2^32) % 2^32
         a_lo = h8_lo + h_lo
         h8_lo = a_lo % 2^32
         h8_hi = (h8_hi + h_hi + (a_lo - h8_lo) / 2^32) % 2^32
      end
      H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8] = h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo
      H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8] = h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi
   end


   if branch == "LIB32" then

      function md5_feed_64(H, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 64
         local W, K, md5_next_shift = common_W, md5_K, md5_next_shift
         local h1, h2, h3, h4 = H[1], H[2], H[3], H[4]
         for pos = offs, offs + size - 1, 64 do
            for j = 1, 16 do
               pos = pos + 4
               local a, b, c, d = byte(str, pos - 3, pos)
               W[j] = ((d * 256 + c) * 256 + b) * 256 + a
            end
            local a, b, c, d = h1, h2, h3, h4
            local s = 25
            for j = 1, 16 do
               local F = ROR(AND(b, c) + AND(-1-b, d) + a + K[j] + W[j], s) + b
               s = md5_next_shift[s]
               a = d
               d = c
               c = b
               b = F
            end
            s = 27
            for j = 17, 32 do
               local F = ROR(AND(d, b) + AND(-1-d, c) + a + K[j] + W[(5*j-4) % 16 + 1], s) + b
               s = md5_next_shift[s]
               a = d
               d = c
               c = b
               b = F
            end
            s = 28
            for j = 33, 48 do
               local F = ROR(XOR(XOR(b, c), d) + a + K[j] + W[(3*j+2) % 16 + 1], s) + b
               s = md5_next_shift[s]
               a = d
               d = c
               c = b
               b = F
            end
            s = 26
            for j = 49, 64 do
               local F = ROR(XOR(c, OR(b, -1-d)) + a + K[j] + W[(j*7-7) % 16 + 1], s) + b
               s = md5_next_shift[s]
               a = d
               d = c
               c = b
               b = F
            end
            h1 = (a + h1) % 2^32
            h2 = (b + h2) % 2^32
            h3 = (c + h3) % 2^32
            h4 = (d + h4) % 2^32
         end
         H[1], H[2], H[3], H[4] = h1, h2, h3, h4
      end

   elseif branch == "EMUL" then

      function md5_feed_64(H, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 64
         local W, K, md5_next_shift = common_W, md5_K, md5_next_shift
         local h1, h2, h3, h4 = H[1], H[2], H[3], H[4]
         for pos = offs, offs + size - 1, 64 do
            for j = 1, 16 do
               pos = pos + 4
               local a, b, c, d = byte(str, pos - 3, pos)
               W[j] = ((d * 256 + c) * 256 + b) * 256 + a
            end
            local a, b, c, d = h1, h2, h3, h4
            local s = 25
            for j = 1, 16 do
               local z = (AND(b, c) + AND(-1-b, d) + a + K[j] + W[j]) % 2^32 / 2^s
               local y = z % 1
               s = md5_next_shift[s]
               a = d
               d = c
               c = b
               b = y * 2^32 + (z - y) + b
            end
            s = 27
            for j = 17, 32 do
               local z = (AND(d, b) + AND(-1-d, c) + a + K[j] + W[(5*j-4) % 16 + 1]) % 2^32 / 2^s
               local y = z % 1
               s = md5_next_shift[s]
               a = d
               d = c
               c = b
               b = y * 2^32 + (z - y) + b
            end
            s = 28
            for j = 33, 48 do
               local z = (XOR(XOR(b, c), d) + a + K[j] + W[(3*j+2) % 16 + 1]) % 2^32 / 2^s
               local y = z % 1
               s = md5_next_shift[s]
               a = d
               d = c
               c = b
               b = y * 2^32 + (z - y) + b
            end
            s = 26
            for j = 49, 64 do
               local z = (XOR(c, OR(b, -1-d)) + a + K[j] + W[(j*7-7) % 16 + 1]) % 2^32 / 2^s
               local y = z % 1
               s = md5_next_shift[s]
               a = d
               d = c
               c = b
               b = y * 2^32 + (z - y) + b
            end
            h1 = (a + h1) % 2^32
            h2 = (b + h2) % 2^32
            h3 = (c + h3) % 2^32
            h4 = (d + h4) % 2^32
         end
         H[1], H[2], H[3], H[4] = h1, h2, h3, h4
      end

   end


   function sha1_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W = common_W
      local h1, h2, h3, h4, h5 = H[1], H[2], H[3], H[4], H[5]
      for pos = offs, offs + size - 1, 64 do
         for j = 1, 16 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)
            W[j] = ((a * 256 + b) * 256 + c) * 256 + d
         end
         for j = 17, 80 do
            local a = XOR(W[j-3], W[j-8], W[j-14], W[j-16]) % 2^32 * 2
            local b = a % 2^32
            W[j] = b + (a - b) / 2^32
         end
         local a, b, c, d, e = h1, h2, h3, h4, h5
         for j = 1, 20 do
            local a5 = a * 2^5
            local z = a5 % 2^32
            z = z + (a5 - z) / 2^32 + AND(b, c) + AND(-1-b, d) + 0x5A827999 + W[j] + e        -- constant = floor(2^30 * sqrt(2))
            e = d
            d = c
            c = b / 2^2
            c = c % 1 * (2^32 - 1) + c
            b = a
            a = z % 2^32
         end
         for j = 21, 40 do
            local a5 = a * 2^5
            local z = a5 % 2^32
            z = z + (a5 - z) / 2^32 + XOR(b, c, d) + 0x6ED9EBA1 + W[j] + e                    -- 2^30 * sqrt(3)
            e = d
            d = c
            c = b / 2^2
            c = c % 1 * (2^32 - 1) + c
            b = a
            a = z % 2^32
         end
         for j = 41, 60 do
            local a5 = a * 2^5
            local z = a5 % 2^32
            z = z + (a5 - z) / 2^32 + AND(d, c) + AND(b, XOR(d, c)) + 0x8F1BBCDC + W[j] + e   -- 2^30 * sqrt(5)
            e = d
            d = c
            c = b / 2^2
            c = c % 1 * (2^32 - 1) + c
            b = a
            a = z % 2^32
         end
         for j = 61, 80 do
            local a5 = a * 2^5
            local z = a5 % 2^32
            z = z + (a5 - z) / 2^32 + XOR(b, c, d) + 0xCA62C1D6 + W[j] + e                    -- 2^30 * sqrt(10)
            e = d
            d = c
            c = b / 2^2
            c = c % 1 * (2^32 - 1) + c
            b = a
            a = z % 2^32
         end
         h1 = (a + h1) % 2^32
         h2 = (b + h2) % 2^32
         h3 = (c + h3) % 2^32
         h4 = (d + h4) % 2^32
         h5 = (e + h5) % 2^32
      end
      H[1], H[2], H[3], H[4], H[5] = h1, h2, h3, h4, h5
   end


   function keccak_feed(lanes_lo, lanes_hi, str, offs, size, block_size_in_bytes)
      -- This is an example of a Lua function having 79 local variables :-)
      -- offs >= 0, size >= 0, size is multiple of block_size_in_bytes, block_size_in_bytes is positive multiple of 8
      local RC_lo, RC_hi = sha3_RC_lo, sha3_RC_hi
      local qwords_qty = block_size_in_bytes / 8
      for pos = offs, offs + size - 1, block_size_in_bytes do
         for j = 1, qwords_qty do
            local a, b, c, d = byte(str, pos + 1, pos + 4)
            lanes_lo[j] = XOR(lanes_lo[j], ((d * 256 + c) * 256 + b) * 256 + a)
            pos = pos + 8
            a, b, c, d = byte(str, pos - 3, pos)
            lanes_hi[j] = XOR(lanes_hi[j], ((d * 256 + c) * 256 + b) * 256 + a)
         end
         local L01_lo, L01_hi, L02_lo, L02_hi, L03_lo, L03_hi, L04_lo, L04_hi, L05_lo, L05_hi, L06_lo, L06_hi, L07_lo, L07_hi, L08_lo, L08_hi,
            L09_lo, L09_hi, L10_lo, L10_hi, L11_lo, L11_hi, L12_lo, L12_hi, L13_lo, L13_hi, L14_lo, L14_hi, L15_lo, L15_hi, L16_lo, L16_hi,
            L17_lo, L17_hi, L18_lo, L18_hi, L19_lo, L19_hi, L20_lo, L20_hi, L21_lo, L21_hi, L22_lo, L22_hi, L23_lo, L23_hi, L24_lo, L24_hi, L25_lo, L25_hi =
            lanes_lo[1], lanes_hi[1], lanes_lo[2], lanes_hi[2], lanes_lo[3], lanes_hi[3], lanes_lo[4], lanes_hi[4], lanes_lo[5], lanes_hi[5],
            lanes_lo[6], lanes_hi[6], lanes_lo[7], lanes_hi[7], lanes_lo[8], lanes_hi[8], lanes_lo[9], lanes_hi[9], lanes_lo[10], lanes_hi[10],
            lanes_lo[11], lanes_hi[11], lanes_lo[12], lanes_hi[12], lanes_lo[13], lanes_hi[13], lanes_lo[14], lanes_hi[14], lanes_lo[15], lanes_hi[15],
            lanes_lo[16], lanes_hi[16], lanes_lo[17], lanes_hi[17], lanes_lo[18], lanes_hi[18], lanes_lo[19], lanes_hi[19], lanes_lo[20], lanes_hi[20],
            lanes_lo[21], lanes_hi[21], lanes_lo[22], lanes_hi[22], lanes_lo[23], lanes_hi[23], lanes_lo[24], lanes_hi[24], lanes_lo[25], lanes_hi[25]
         for round_idx = 1, 24 do
            local C1_lo = XOR(L01_lo, L06_lo, L11_lo, L16_lo, L21_lo)
            local C1_hi = XOR(L01_hi, L06_hi, L11_hi, L16_hi, L21_hi)
            local C2_lo = XOR(L02_lo, L07_lo, L12_lo, L17_lo, L22_lo)
            local C2_hi = XOR(L02_hi, L07_hi, L12_hi, L17_hi, L22_hi)
            local C3_lo = XOR(L03_lo, L08_lo, L13_lo, L18_lo, L23_lo)
            local C3_hi = XOR(L03_hi, L08_hi, L13_hi, L18_hi, L23_hi)
            local C4_lo = XOR(L04_lo, L09_lo, L14_lo, L19_lo, L24_lo)
            local C4_hi = XOR(L04_hi, L09_hi, L14_hi, L19_hi, L24_hi)
            local C5_lo = XOR(L05_lo, L10_lo, L15_lo, L20_lo, L25_lo)
            local C5_hi = XOR(L05_hi, L10_hi, L15_hi, L20_hi, L25_hi)
            local D_lo = XOR(C1_lo, C3_lo * 2 + (C3_hi % 2^32 - C3_hi % 2^31) / 2^31)
            local D_hi = XOR(C1_hi, C3_hi * 2 + (C3_lo % 2^32 - C3_lo % 2^31) / 2^31)
            local T0_lo = XOR(D_lo, L02_lo)
            local T0_hi = XOR(D_hi, L02_hi)
            local T1_lo = XOR(D_lo, L07_lo)
            local T1_hi = XOR(D_hi, L07_hi)
            local T2_lo = XOR(D_lo, L12_lo)
            local T2_hi = XOR(D_hi, L12_hi)
            local T3_lo = XOR(D_lo, L17_lo)
            local T3_hi = XOR(D_hi, L17_hi)
            local T4_lo = XOR(D_lo, L22_lo)
            local T4_hi = XOR(D_hi, L22_hi)
            L02_lo = (T1_lo % 2^32 - T1_lo % 2^20) / 2^20 + T1_hi * 2^12
            L02_hi = (T1_hi % 2^32 - T1_hi % 2^20) / 2^20 + T1_lo * 2^12
            L07_lo = (T3_lo % 2^32 - T3_lo % 2^19) / 2^19 + T3_hi * 2^13
            L07_hi = (T3_hi % 2^32 - T3_hi % 2^19) / 2^19 + T3_lo * 2^13
            L12_lo = T0_lo * 2 + (T0_hi % 2^32 - T0_hi % 2^31) / 2^31
            L12_hi = T0_hi * 2 + (T0_lo % 2^32 - T0_lo % 2^31) / 2^31
            L17_lo = T2_lo * 2^10 + (T2_hi % 2^32 - T2_hi % 2^22) / 2^22
            L17_hi = T2_hi * 2^10 + (T2_lo % 2^32 - T2_lo % 2^22) / 2^22
            L22_lo = T4_lo * 2^2 + (T4_hi % 2^32 - T4_hi % 2^30) / 2^30
            L22_hi = T4_hi * 2^2 + (T4_lo % 2^32 - T4_lo % 2^30) / 2^30
            D_lo = XOR(C2_lo, C4_lo * 2 + (C4_hi % 2^32 - C4_hi % 2^31) / 2^31)
            D_hi = XOR(C2_hi, C4_hi * 2 + (C4_lo % 2^32 - C4_lo % 2^31) / 2^31)
            T0_lo = XOR(D_lo, L03_lo)
            T0_hi = XOR(D_hi, L03_hi)
            T1_lo = XOR(D_lo, L08_lo)
            T1_hi = XOR(D_hi, L08_hi)
            T2_lo = XOR(D_lo, L13_lo)
            T2_hi = XOR(D_hi, L13_hi)
            T3_lo = XOR(D_lo, L18_lo)
            T3_hi = XOR(D_hi, L18_hi)
            T4_lo = XOR(D_lo, L23_lo)
            T4_hi = XOR(D_hi, L23_hi)
            L03_lo = (T2_lo % 2^32 - T2_lo % 2^21) / 2^21 + T2_hi * 2^11
            L03_hi = (T2_hi % 2^32 - T2_hi % 2^21) / 2^21 + T2_lo * 2^11
            L08_lo = (T4_lo % 2^32 - T4_lo % 2^3) / 2^3 + T4_hi * 2^29 % 2^32
            L08_hi = (T4_hi % 2^32 - T4_hi % 2^3) / 2^3 + T4_lo * 2^29 % 2^32
            L13_lo = T1_lo * 2^6 + (T1_hi % 2^32 - T1_hi % 2^26) / 2^26
            L13_hi = T1_hi * 2^6 + (T1_lo % 2^32 - T1_lo % 2^26) / 2^26
            L18_lo = T3_lo * 2^15 + (T3_hi % 2^32 - T3_hi % 2^17) / 2^17
            L18_hi = T3_hi * 2^15 + (T3_lo % 2^32 - T3_lo % 2^17) / 2^17
            L23_lo = (T0_lo % 2^32 - T0_lo % 2^2) / 2^2 + T0_hi * 2^30 % 2^32
            L23_hi = (T0_hi % 2^32 - T0_hi % 2^2) / 2^2 + T0_lo * 2^30 % 2^32
            D_lo = XOR(C3_lo, C5_lo * 2 + (C5_hi % 2^32 - C5_hi % 2^31) / 2^31)
            D_hi = XOR(C3_hi, C5_hi * 2 + (C5_lo % 2^32 - C5_lo % 2^31) / 2^31)
            T0_lo = XOR(D_lo, L04_lo)
            T0_hi = XOR(D_hi, L04_hi)
            T1_lo = XOR(D_lo, L09_lo)
            T1_hi = XOR(D_hi, L09_hi)
            T2_lo = XOR(D_lo, L14_lo)
            T2_hi = XOR(D_hi, L14_hi)
            T3_lo = XOR(D_lo, L19_lo)
            T3_hi = XOR(D_hi, L19_hi)
            T4_lo = XOR(D_lo, L24_lo)
            T4_hi = XOR(D_hi, L24_hi)
            L04_lo = T3_lo * 2^21 % 2^32 + (T3_hi % 2^32 - T3_hi % 2^11) / 2^11
            L04_hi = T3_hi * 2^21 % 2^32 + (T3_lo % 2^32 - T3_lo % 2^11) / 2^11
            L09_lo = T0_lo * 2^28 % 2^32 + (T0_hi % 2^32 - T0_hi % 2^4) / 2^4
            L09_hi = T0_hi * 2^28 % 2^32 + (T0_lo % 2^32 - T0_lo % 2^4) / 2^4
            L14_lo = T2_lo * 2^25 % 2^32 + (T2_hi % 2^32 - T2_hi % 2^7) / 2^7
            L14_hi = T2_hi * 2^25 % 2^32 + (T2_lo % 2^32 - T2_lo % 2^7) / 2^7
            L19_lo = (T4_lo % 2^32 - T4_lo % 2^8) / 2^8 + T4_hi * 2^24 % 2^32
            L19_hi = (T4_hi % 2^32 - T4_hi % 2^8) / 2^8 + T4_lo * 2^24 % 2^32
            L24_lo = (T1_lo % 2^32 - T1_lo % 2^9) / 2^9 + T1_hi * 2^23 % 2^32
            L24_hi = (T1_hi % 2^32 - T1_hi % 2^9) / 2^9 + T1_lo * 2^23 % 2^32
            D_lo = XOR(C4_lo, C1_lo * 2 + (C1_hi % 2^32 - C1_hi % 2^31) / 2^31)
            D_hi = XOR(C4_hi, C1_hi * 2 + (C1_lo % 2^32 - C1_lo % 2^31) / 2^31)
            T0_lo = XOR(D_lo, L05_lo)
            T0_hi = XOR(D_hi, L05_hi)
            T1_lo = XOR(D_lo, L10_lo)
            T1_hi = XOR(D_hi, L10_hi)
            T2_lo = XOR(D_lo, L15_lo)
            T2_hi = XOR(D_hi, L15_hi)
            T3_lo = XOR(D_lo, L20_lo)
            T3_hi = XOR(D_hi, L20_hi)
            T4_lo = XOR(D_lo, L25_lo)
            T4_hi = XOR(D_hi, L25_hi)
            L05_lo = T4_lo * 2^14 + (T4_hi % 2^32 - T4_hi % 2^18) / 2^18
            L05_hi = T4_hi * 2^14 + (T4_lo % 2^32 - T4_lo % 2^18) / 2^18
            L10_lo = T1_lo * 2^20 % 2^32 + (T1_hi % 2^32 - T1_hi % 2^12) / 2^12
            L10_hi = T1_hi * 2^20 % 2^32 + (T1_lo % 2^32 - T1_lo % 2^12) / 2^12
            L15_lo = T3_lo * 2^8 + (T3_hi % 2^32 - T3_hi % 2^24) / 2^24
            L15_hi = T3_hi * 2^8 + (T3_lo % 2^32 - T3_lo % 2^24) / 2^24
            L20_lo = T0_lo * 2^27 % 2^32 + (T0_hi % 2^32 - T0_hi % 2^5) / 2^5
            L20_hi = T0_hi * 2^27 % 2^32 + (T0_lo % 2^32 - T0_lo % 2^5) / 2^5
            L25_lo = (T2_lo % 2^32 - T2_lo % 2^25) / 2^25 + T2_hi * 2^7
            L25_hi = (T2_hi % 2^32 - T2_hi % 2^25) / 2^25 + T2_lo * 2^7
            D_lo = XOR(C5_lo, C2_lo * 2 + (C2_hi % 2^32 - C2_hi % 2^31) / 2^31)
            D_hi = XOR(C5_hi, C2_hi * 2 + (C2_lo % 2^32 - C2_lo % 2^31) / 2^31)
            T1_lo = XOR(D_lo, L06_lo)
            T1_hi = XOR(D_hi, L06_hi)
            T2_lo = XOR(D_lo, L11_lo)
            T2_hi = XOR(D_hi, L11_hi)
            T3_lo = XOR(D_lo, L16_lo)
            T3_hi = XOR(D_hi, L16_hi)
            T4_lo = XOR(D_lo, L21_lo)
            T4_hi = XOR(D_hi, L21_hi)
            L06_lo = T2_lo * 2^3 + (T2_hi % 2^32 - T2_hi % 2^29) / 2^29
            L06_hi = T2_hi * 2^3 + (T2_lo % 2^32 - T2_lo % 2^29) / 2^29
            L11_lo = T4_lo * 2^18 + (T4_hi % 2^32 - T4_hi % 2^14) / 2^14
            L11_hi = T4_hi * 2^18 + (T4_lo % 2^32 - T4_lo % 2^14) / 2^14
            L16_lo = (T1_lo % 2^32 - T1_lo % 2^28) / 2^28 + T1_hi * 2^4
            L16_hi = (T1_hi % 2^32 - T1_hi % 2^28) / 2^28 + T1_lo * 2^4
            L21_lo = (T3_lo % 2^32 - T3_lo % 2^23) / 2^23 + T3_hi * 2^9
            L21_hi = (T3_hi % 2^32 - T3_hi % 2^23) / 2^23 + T3_lo * 2^9
            L01_lo = XOR(D_lo, L01_lo)
            L01_hi = XOR(D_hi, L01_hi)
            L01_lo, L02_lo, L03_lo, L04_lo, L05_lo = XOR(L01_lo, AND(-1-L02_lo, L03_lo)), XOR(L02_lo, AND(-1-L03_lo, L04_lo)), XOR(L03_lo, AND(-1-L04_lo, L05_lo)), XOR(L04_lo, AND(-1-L05_lo, L01_lo)), XOR(L05_lo, AND(-1-L01_lo, L02_lo))
            L01_hi, L02_hi, L03_hi, L04_hi, L05_hi = XOR(L01_hi, AND(-1-L02_hi, L03_hi)), XOR(L02_hi, AND(-1-L03_hi, L04_hi)), XOR(L03_hi, AND(-1-L04_hi, L05_hi)), XOR(L04_hi, AND(-1-L05_hi, L01_hi)), XOR(L05_hi, AND(-1-L01_hi, L02_hi))
            L06_lo, L07_lo, L08_lo, L09_lo, L10_lo = XOR(L09_lo, AND(-1-L10_lo, L06_lo)), XOR(L10_lo, AND(-1-L06_lo, L07_lo)), XOR(L06_lo, AND(-1-L07_lo, L08_lo)), XOR(L07_lo, AND(-1-L08_lo, L09_lo)), XOR(L08_lo, AND(-1-L09_lo, L10_lo))
            L06_hi, L07_hi, L08_hi, L09_hi, L10_hi = XOR(L09_hi, AND(-1-L10_hi, L06_hi)), XOR(L10_hi, AND(-1-L06_hi, L07_hi)), XOR(L06_hi, AND(-1-L07_hi, L08_hi)), XOR(L07_hi, AND(-1-L08_hi, L09_hi)), XOR(L08_hi, AND(-1-L09_hi, L10_hi))
            L11_lo, L12_lo, L13_lo, L14_lo, L15_lo = XOR(L12_lo, AND(-1-L13_lo, L14_lo)), XOR(L13_lo, AND(-1-L14_lo, L15_lo)), XOR(L14_lo, AND(-1-L15_lo, L11_lo)), XOR(L15_lo, AND(-1-L11_lo, L12_lo)), XOR(L11_lo, AND(-1-L12_lo, L13_lo))
            L11_hi, L12_hi, L13_hi, L14_hi, L15_hi = XOR(L12_hi, AND(-1-L13_hi, L14_hi)), XOR(L13_hi, AND(-1-L14_hi, L15_hi)), XOR(L14_hi, AND(-1-L15_hi, L11_hi)), XOR(L15_hi, AND(-1-L11_hi, L12_hi)), XOR(L11_hi, AND(-1-L12_hi, L13_hi))
            L16_lo, L17_lo, L18_lo, L19_lo, L20_lo = XOR(L20_lo, AND(-1-L16_lo, L17_lo)), XOR(L16_lo, AND(-1-L17_lo, L18_lo)), XOR(L17_lo, AND(-1-L18_lo, L19_lo)), XOR(L18_lo, AND(-1-L19_lo, L20_lo)), XOR(L19_lo, AND(-1-L20_lo, L16_lo))
            L16_hi, L17_hi, L18_hi, L19_hi, L20_hi = XOR(L20_hi, AND(-1-L16_hi, L17_hi)), XOR(L16_hi, AND(-1-L17_hi, L18_hi)), XOR(L17_hi, AND(-1-L18_hi, L19_hi)), XOR(L18_hi, AND(-1-L19_hi, L20_hi)), XOR(L19_hi, AND(-1-L20_hi, L16_hi))
            L21_lo, L22_lo, L23_lo, L24_lo, L25_lo = XOR(L23_lo, AND(-1-L24_lo, L25_lo)), XOR(L24_lo, AND(-1-L25_lo, L21_lo)), XOR(L25_lo, AND(-1-L21_lo, L22_lo)), XOR(L21_lo, AND(-1-L22_lo, L23_lo)), XOR(L22_lo, AND(-1-L23_lo, L24_lo))
            L21_hi, L22_hi, L23_hi, L24_hi, L25_hi = XOR(L23_hi, AND(-1-L24_hi, L25_hi)), XOR(L24_hi, AND(-1-L25_hi, L21_hi)), XOR(L25_hi, AND(-1-L21_hi, L22_hi)), XOR(L21_hi, AND(-1-L22_hi, L23_hi)), XOR(L22_hi, AND(-1-L23_hi, L24_hi))
            L01_lo = XOR(L01_lo, RC_lo[round_idx])
            L01_hi = L01_hi + RC_hi[round_idx]      -- RC_hi[] is either 0 or 0x80000000, so we could use fast addition instead of slow XOR
         end
         lanes_lo[1]  = L01_lo;  lanes_hi[1]  = L01_hi
         lanes_lo[2]  = L02_lo;  lanes_hi[2]  = L02_hi
         lanes_lo[3]  = L03_lo;  lanes_hi[3]  = L03_hi
         lanes_lo[4]  = L04_lo;  lanes_hi[4]  = L04_hi
         lanes_lo[5]  = L05_lo;  lanes_hi[5]  = L05_hi
         lanes_lo[6]  = L06_lo;  lanes_hi[6]  = L06_hi
         lanes_lo[7]  = L07_lo;  lanes_hi[7]  = L07_hi
         lanes_lo[8]  = L08_lo;  lanes_hi[8]  = L08_hi
         lanes_lo[9]  = L09_lo;  lanes_hi[9]  = L09_hi
         lanes_lo[10] = L10_lo;  lanes_hi[10] = L10_hi
         lanes_lo[11] = L11_lo;  lanes_hi[11] = L11_hi
         lanes_lo[12] = L12_lo;  lanes_hi[12] = L12_hi
         lanes_lo[13] = L13_lo;  lanes_hi[13] = L13_hi
         lanes_lo[14] = L14_lo;  lanes_hi[14] = L14_hi
         lanes_lo[15] = L15_lo;  lanes_hi[15] = L15_hi
         lanes_lo[16] = L16_lo;  lanes_hi[16] = L16_hi
         lanes_lo[17] = L17_lo;  lanes_hi[17] = L17_hi
         lanes_lo[18] = L18_lo;  lanes_hi[18] = L18_hi
         lanes_lo[19] = L19_lo;  lanes_hi[19] = L19_hi
         lanes_lo[20] = L20_lo;  lanes_hi[20] = L20_hi
         lanes_lo[21] = L21_lo;  lanes_hi[21] = L21_hi
         lanes_lo[22] = L22_lo;  lanes_hi[22] = L22_hi
         lanes_lo[23] = L23_lo;  lanes_hi[23] = L23_hi
         lanes_lo[24] = L24_lo;  lanes_hi[24] = L24_hi
         lanes_lo[25] = L25_lo;  lanes_hi[25] = L25_hi
      end
   end


   function blake2s_feed_64(H, str, offs, size, bytes_compressed, last_block_size, is_last_node)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W = common_W
      local h1, h2, h3, h4, h5, h6, h7, h8 = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
      for pos = offs, offs + size - 1, 64 do
         if str then
            for j = 1, 16 do
               pos = pos + 4
               local a, b, c, d = byte(str, pos - 3, pos)
               W[j] = ((d * 256 + c) * 256 + b) * 256 + a
            end
         end
         local v0, v1, v2, v3, v4, v5, v6, v7 = h1, h2, h3, h4, h5, h6, h7, h8
         local v8, v9, vA, vB, vC, vD, vE, vF = sha2_H_hi[1], sha2_H_hi[2], sha2_H_hi[3], sha2_H_hi[4], sha2_H_hi[5], sha2_H_hi[6], sha2_H_hi[7], sha2_H_hi[8]
         bytes_compressed = bytes_compressed + (last_block_size or 64)
         local t0 = bytes_compressed % 2^32
         local t1 = (bytes_compressed - t0) / 2^32
         vC = XOR(vC, t0)  -- t0 = low_4_bytes(bytes_compressed)
         vD = XOR(vD, t1)  -- t1 = high_4_bytes(bytes_compressed)
         if last_block_size then  -- flag f0
            vE = -1 - vE
         end
         if is_last_node then  -- flag f1
            vF = -1 - vF
         end
         for j = 1, 10 do
            local row = sigma[j]
            v0 = v0 + v4 + W[row[1]]
            vC = XOR(vC, v0) % 2^32 / 2^16
            vC = vC % 1 * (2^32 - 1) + vC
            v8 = v8 + vC
            v4 = XOR(v4, v8) % 2^32 / 2^12
            v4 = v4 % 1 * (2^32 - 1) + v4
            v0 = v0 + v4 + W[row[2]]
            vC = XOR(vC, v0) % 2^32 / 2^8
            vC = vC % 1 * (2^32 - 1) + vC
            v8 = v8 + vC
            v4 = XOR(v4, v8) % 2^32 / 2^7
            v4 = v4 % 1 * (2^32 - 1) + v4
            v1 = v1 + v5 + W[row[3]]
            vD = XOR(vD, v1) % 2^32 / 2^16
            vD = vD % 1 * (2^32 - 1) + vD
            v9 = v9 + vD
            v5 = XOR(v5, v9) % 2^32 / 2^12
            v5 = v5 % 1 * (2^32 - 1) + v5
            v1 = v1 + v5 + W[row[4]]
            vD = XOR(vD, v1) % 2^32 / 2^8
            vD = vD % 1 * (2^32 - 1) + vD
            v9 = v9 + vD
            v5 = XOR(v5, v9) % 2^32 / 2^7
            v5 = v5 % 1 * (2^32 - 1) + v5
            v2 = v2 + v6 + W[row[5]]
            vE = XOR(vE, v2) % 2^32 / 2^16
            vE = vE % 1 * (2^32 - 1) + vE
            vA = vA + vE
            v6 = XOR(v6, vA) % 2^32 / 2^12
            v6 = v6 % 1 * (2^32 - 1) + v6
            v2 = v2 + v6 + W[row[6]]
            vE = XOR(vE, v2) % 2^32 / 2^8
            vE = vE % 1 * (2^32 - 1) + vE
            vA = vA + vE
            v6 = XOR(v6, vA) % 2^32 / 2^7
            v6 = v6 % 1 * (2^32 - 1) + v6
            v3 = v3 + v7 + W[row[7]]
            vF = XOR(vF, v3) % 2^32 / 2^16
            vF = vF % 1 * (2^32 - 1) + vF
            vB = vB + vF
            v7 = XOR(v7, vB) % 2^32 / 2^12
            v7 = v7 % 1 * (2^32 - 1) + v7
            v3 = v3 + v7 + W[row[8]]
            vF = XOR(vF, v3) % 2^32 / 2^8
            vF = vF % 1 * (2^32 - 1) + vF
            vB = vB + vF
            v7 = XOR(v7, vB) % 2^32 / 2^7
            v7 = v7 % 1 * (2^32 - 1) + v7
            v0 = v0 + v5 + W[row[9]]
            vF = XOR(vF, v0) % 2^32 / 2^16
            vF = vF % 1 * (2^32 - 1) + vF
            vA = vA + vF
            v5 = XOR(v5, vA) % 2^32 / 2^12
            v5 = v5 % 1 * (2^32 - 1) + v5
            v0 = v0 + v5 + W[row[10]]
            vF = XOR(vF, v0) % 2^32 / 2^8
            vF = vF % 1 * (2^32 - 1) + vF
            vA = vA + vF
            v5 = XOR(v5, vA) % 2^32 / 2^7
            v5 = v5 % 1 * (2^32 - 1) + v5
            v1 = v1 + v6 + W[row[11]]
            vC = XOR(vC, v1) % 2^32 / 2^16
            vC = vC % 1 * (2^32 - 1) + vC
            vB = vB + vC
            v6 = XOR(v6, vB) % 2^32 / 2^12
            v6 = v6 % 1 * (2^32 - 1) + v6
            v1 = v1 + v6 + W[row[12]]
            vC = XOR(vC, v1) % 2^32 / 2^8
            vC = vC % 1 * (2^32 - 1) + vC
            vB = vB + vC
            v6 = XOR(v6, vB) % 2^32 / 2^7
            v6 = v6 % 1 * (2^32 - 1) + v6
            v2 = v2 + v7 + W[row[13]]
            vD = XOR(vD, v2) % 2^32 / 2^16
            vD = vD % 1 * (2^32 - 1) + vD
            v8 = v8 + vD
            v7 = XOR(v7, v8) % 2^32 / 2^12
            v7 = v7 % 1 * (2^32 - 1) + v7
            v2 = v2 + v7 + W[row[14]]
            vD = XOR(vD, v2) % 2^32 / 2^8
            vD = vD % 1 * (2^32 - 1) + vD
            v8 = v8 + vD
            v7 = XOR(v7, v8) % 2^32 / 2^7
            v7 = v7 % 1 * (2^32 - 1) + v7
            v3 = v3 + v4 + W[row[15]]
            vE = XOR(vE, v3) % 2^32 / 2^16
            vE = vE % 1 * (2^32 - 1) + vE
            v9 = v9 + vE
            v4 = XOR(v4, v9) % 2^32 / 2^12
            v4 = v4 % 1 * (2^32 - 1) + v4
            v3 = v3 + v4 + W[row[16]]
            vE = XOR(vE, v3) % 2^32 / 2^8
            vE = vE % 1 * (2^32 - 1) + vE
            v9 = v9 + vE
            v4 = XOR(v4, v9) % 2^32 / 2^7
            v4 = v4 % 1 * (2^32 - 1) + v4
         end
         h1 = XOR(h1, v0, v8)
         h2 = XOR(h2, v1, v9)
         h3 = XOR(h3, v2, vA)
         h4 = XOR(h4, v3, vB)
         h5 = XOR(h5, v4, vC)
         h6 = XOR(h6, v5, vD)
         h7 = XOR(h7, v6, vE)
         h8 = XOR(h8, v7, vF)
      end
      H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8] = h1, h2, h3, h4, h5, h6, h7, h8
      return bytes_compressed
   end


   function blake2b_feed_128(H_lo, H_hi, str, offs, size, bytes_compressed, last_block_size, is_last_node)
      -- offs >= 0, size >= 0, size is multiple of 128
      local W = common_W
      local h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo = H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8]
      local h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi = H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8]
      for pos = offs, offs + size - 1, 128 do
         if str then
            for j = 1, 32 do
               pos = pos + 4
               local a, b, c, d = byte(str, pos - 3, pos)
               W[j] = ((d * 256 + c) * 256 + b) * 256 + a
            end
         end
         local v0_lo, v1_lo, v2_lo, v3_lo, v4_lo, v5_lo, v6_lo, v7_lo = h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo
         local v0_hi, v1_hi, v2_hi, v3_hi, v4_hi, v5_hi, v6_hi, v7_hi = h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi
         local v8_lo, v9_lo, vA_lo, vB_lo, vC_lo, vD_lo, vE_lo, vF_lo = sha2_H_lo[1], sha2_H_lo[2], sha2_H_lo[3], sha2_H_lo[4], sha2_H_lo[5], sha2_H_lo[6], sha2_H_lo[7], sha2_H_lo[8]
         local v8_hi, v9_hi, vA_hi, vB_hi, vC_hi, vD_hi, vE_hi, vF_hi = sha2_H_hi[1], sha2_H_hi[2], sha2_H_hi[3], sha2_H_hi[4], sha2_H_hi[5], sha2_H_hi[6], sha2_H_hi[7], sha2_H_hi[8]
         bytes_compressed = bytes_compressed + (last_block_size or 128)
         local t0_lo = bytes_compressed % 2^32
         local t0_hi = (bytes_compressed - t0_lo) / 2^32
         vC_lo = XOR(vC_lo, t0_lo)  -- t0 = low_8_bytes(bytes_compressed)
         vC_hi = XOR(vC_hi, t0_hi)
         -- t1 = high_8_bytes(bytes_compressed) = 0,  message length is always below 2^53 bytes
         if last_block_size then  -- flag f0
            vE_lo = -1 - vE_lo
            vE_hi = -1 - vE_hi
         end
         if is_last_node then  -- flag f1
            vF_lo = -1 - vF_lo
            vF_hi = -1 - vF_hi
         end
         for j = 1, 12 do
            local row = sigma[j]
            local k = row[1] * 2
            local z = v0_lo % 2^32 + v4_lo % 2^32 + W[k-1]
            v0_lo = z % 2^32
            v0_hi = v0_hi + v4_hi + (z - v0_lo) / 2^32 + W[k]
            vC_lo, vC_hi = XOR(vC_hi, v0_hi), XOR(vC_lo, v0_lo)
            z = v8_lo % 2^32 + vC_lo % 2^32
            v8_lo = z % 2^32
            v8_hi = v8_hi + vC_hi + (z - v8_lo) / 2^32
            v4_lo, v4_hi = XOR(v4_lo, v8_lo), XOR(v4_hi, v8_hi)
            local z_lo, z_hi = v4_lo % 2^24, v4_hi % 2^24
            v4_lo, v4_hi = (v4_lo - z_lo) / 2^24 % 2^8 + z_hi * 2^8, (v4_hi - z_hi) / 2^24 % 2^8 + z_lo * 2^8
            k = row[2] * 2
            z = v0_lo % 2^32 + v4_lo % 2^32 + W[k-1]
            v0_lo = z % 2^32
            v0_hi = v0_hi + v4_hi + (z - v0_lo) / 2^32 + W[k]
            vC_lo, vC_hi = XOR(vC_lo, v0_lo), XOR(vC_hi, v0_hi)
            z_lo, z_hi = vC_lo % 2^16, vC_hi % 2^16
            vC_lo, vC_hi = (vC_lo - z_lo) / 2^16 % 2^16 + z_hi * 2^16, (vC_hi - z_hi) / 2^16 % 2^16 + z_lo * 2^16
            z = v8_lo % 2^32 + vC_lo % 2^32
            v8_lo = z % 2^32
            v8_hi = v8_hi + vC_hi + (z - v8_lo) / 2^32
            v4_lo, v4_hi = XOR(v4_lo, v8_lo), XOR(v4_hi, v8_hi)
            z_lo, z_hi = v4_lo % 2^31, v4_hi % 2^31
            v4_lo, v4_hi = z_lo * 2^1 + (v4_hi - z_hi) / 2^31 % 2^1, z_hi * 2^1 + (v4_lo - z_lo) / 2^31 % 2^1
            k = row[3] * 2
            z = v1_lo % 2^32 + v5_lo % 2^32 + W[k-1]
            v1_lo = z % 2^32
            v1_hi = v1_hi + v5_hi + (z - v1_lo) / 2^32 + W[k]
            vD_lo, vD_hi = XOR(vD_hi, v1_hi), XOR(vD_lo, v1_lo)
            z = v9_lo % 2^32 + vD_lo % 2^32
            v9_lo = z % 2^32
            v9_hi = v9_hi + vD_hi + (z - v9_lo) / 2^32
            v5_lo, v5_hi = XOR(v5_lo, v9_lo), XOR(v5_hi, v9_hi)
            z_lo, z_hi = v5_lo % 2^24, v5_hi % 2^24
            v5_lo, v5_hi = (v5_lo - z_lo) / 2^24 % 2^8 + z_hi * 2^8, (v5_hi - z_hi) / 2^24 % 2^8 + z_lo * 2^8
            k = row[4] * 2
            z = v1_lo % 2^32 + v5_lo % 2^32 + W[k-1]
            v1_lo = z % 2^32
            v1_hi = v1_hi + v5_hi + (z - v1_lo) / 2^32 + W[k]
            vD_lo, vD_hi = XOR(vD_lo, v1_lo), XOR(vD_hi, v1_hi)
            z_lo, z_hi = vD_lo % 2^16, vD_hi % 2^16
            vD_lo, vD_hi = (vD_lo - z_lo) / 2^16 % 2^16 + z_hi * 2^16, (vD_hi - z_hi) / 2^16 % 2^16 + z_lo * 2^16
            z = v9_lo % 2^32 + vD_lo % 2^32
            v9_lo = z % 2^32
            v9_hi = v9_hi + vD_hi + (z - v9_lo) / 2^32
            v5_lo, v5_hi = XOR(v5_lo, v9_lo), XOR(v5_hi, v9_hi)
            z_lo, z_hi = v5_lo % 2^31, v5_hi % 2^31
            v5_lo, v5_hi = z_lo * 2^1 + (v5_hi - z_hi) / 2^31 % 2^1, z_hi * 2^1 + (v5_lo - z_lo) / 2^31 % 2^1
            k = row[5] * 2
            z = v2_lo % 2^32 + v6_lo % 2^32 + W[k-1]
            v2_lo = z % 2^32
            v2_hi = v2_hi + v6_hi + (z - v2_lo) / 2^32 + W[k]
            vE_lo, vE_hi = XOR(vE_hi, v2_hi), XOR(vE_lo, v2_lo)
            z = vA_lo % 2^32 + vE_lo % 2^32
            vA_lo = z % 2^32
            vA_hi = vA_hi + vE_hi + (z - vA_lo) / 2^32
            v6_lo, v6_hi = XOR(v6_lo, vA_lo), XOR(v6_hi, vA_hi)
            z_lo, z_hi = v6_lo % 2^24, v6_hi % 2^24
            v6_lo, v6_hi = (v6_lo - z_lo) / 2^24 % 2^8 + z_hi * 2^8, (v6_hi - z_hi) / 2^24 % 2^8 + z_lo * 2^8
            k = row[6] * 2
            z = v2_lo % 2^32 + v6_lo % 2^32 + W[k-1]
            v2_lo = z % 2^32
            v2_hi = v2_hi + v6_hi + (z - v2_lo) / 2^32 + W[k]
            vE_lo, vE_hi = XOR(vE_lo, v2_lo), XOR(vE_hi, v2_hi)
            z_lo, z_hi = vE_lo % 2^16, vE_hi % 2^16
            vE_lo, vE_hi = (vE_lo - z_lo) / 2^16 % 2^16 + z_hi * 2^16, (vE_hi - z_hi) / 2^16 % 2^16 + z_lo * 2^16
            z = vA_lo % 2^32 + vE_lo % 2^32
            vA_lo = z % 2^32
            vA_hi = vA_hi + vE_hi + (z - vA_lo) / 2^32
            v6_lo, v6_hi = XOR(v6_lo, vA_lo), XOR(v6_hi, vA_hi)
            z_lo, z_hi = v6_lo % 2^31, v6_hi % 2^31
            v6_lo, v6_hi = z_lo * 2^1 + (v6_hi - z_hi) / 2^31 % 2^1, z_hi * 2^1 + (v6_lo - z_lo) / 2^31 % 2^1
            k = row[7] * 2
            z = v3_lo % 2^32 + v7_lo % 2^32 + W[k-1]
            v3_lo = z % 2^32
            v3_hi = v3_hi + v7_hi + (z - v3_lo) / 2^32 + W[k]
            vF_lo, vF_hi = XOR(vF_hi, v3_hi), XOR(vF_lo, v3_lo)
            z = vB_lo % 2^32 + vF_lo % 2^32
            vB_lo = z % 2^32
            vB_hi = vB_hi + vF_hi + (z - vB_lo) / 2^32
            v7_lo, v7_hi = XOR(v7_lo, vB_lo), XOR(v7_hi, vB_hi)
            z_lo, z_hi = v7_lo % 2^24, v7_hi % 2^24
            v7_lo, v7_hi = (v7_lo - z_lo) / 2^24 % 2^8 + z_hi * 2^8, (v7_hi - z_hi) / 2^24 % 2^8 + z_lo * 2^8
            k = row[8] * 2
            z = v3_lo % 2^32 + v7_lo % 2^32 + W[k-1]
            v3_lo = z % 2^32
            v3_hi = v3_hi + v7_hi + (z - v3_lo) / 2^32 + W[k]
            vF_lo, vF_hi = XOR(vF_lo, v3_lo), XOR(vF_hi, v3_hi)
            z_lo, z_hi = vF_lo % 2^16, vF_hi % 2^16
            vF_lo, vF_hi = (vF_lo - z_lo) / 2^16 % 2^16 + z_hi * 2^16, (vF_hi - z_hi) / 2^16 % 2^16 + z_lo * 2^16
            z = vB_lo % 2^32 + vF_lo % 2^32
            vB_lo = z % 2^32
            vB_hi = vB_hi + vF_hi + (z - vB_lo) / 2^32
            v7_lo, v7_hi = XOR(v7_lo, vB_lo), XOR(v7_hi, vB_hi)
            z_lo, z_hi = v7_lo % 2^31, v7_hi % 2^31
            v7_lo, v7_hi = z_lo * 2^1 + (v7_hi - z_hi) / 2^31 % 2^1, z_hi * 2^1 + (v7_lo - z_lo) / 2^31 % 2^1
            k = row[9] * 2
            z = v0_lo % 2^32 + v5_lo % 2^32 + W[k-1]
            v0_lo = z % 2^32
            v0_hi = v0_hi + v5_hi + (z - v0_lo) / 2^32 + W[k]
            vF_lo, vF_hi = XOR(vF_hi, v0_hi), XOR(vF_lo, v0_lo)
            z = vA_lo % 2^32 + vF_lo % 2^32
            vA_lo = z % 2^32
            vA_hi = vA_hi + vF_hi + (z - vA_lo) / 2^32
            v5_lo, v5_hi = XOR(v5_lo, vA_lo), XOR(v5_hi, vA_hi)
            z_lo, z_hi = v5_lo % 2^24, v5_hi % 2^24
            v5_lo, v5_hi = (v5_lo - z_lo) / 2^24 % 2^8 + z_hi * 2^8, (v5_hi - z_hi) / 2^24 % 2^8 + z_lo * 2^8
            k = row[10] * 2
            z = v0_lo % 2^32 + v5_lo % 2^32 + W[k-1]
            v0_lo = z % 2^32
            v0_hi = v0_hi + v5_hi + (z - v0_lo) / 2^32 + W[k]
            vF_lo, vF_hi = XOR(vF_lo, v0_lo), XOR(vF_hi, v0_hi)
            z_lo, z_hi = vF_lo % 2^16, vF_hi % 2^16
            vF_lo, vF_hi = (vF_lo - z_lo) / 2^16 % 2^16 + z_hi * 2^16, (vF_hi - z_hi) / 2^16 % 2^16 + z_lo * 2^16
            z = vA_lo % 2^32 + vF_lo % 2^32
            vA_lo = z % 2^32
            vA_hi = vA_hi + vF_hi + (z - vA_lo) / 2^32
            v5_lo, v5_hi = XOR(v5_lo, vA_lo), XOR(v5_hi, vA_hi)
            z_lo, z_hi = v5_lo % 2^31, v5_hi % 2^31
            v5_lo, v5_hi = z_lo * 2^1 + (v5_hi - z_hi) / 2^31 % 2^1, z_hi * 2^1 + (v5_lo - z_lo) / 2^31 % 2^1
            k = row[11] * 2
            z = v1_lo % 2^32 + v6_lo % 2^32 + W[k-1]
            v1_lo = z % 2^32
            v1_hi = v1_hi + v6_hi + (z - v1_lo) / 2^32 + W[k]
            vC_lo, vC_hi = XOR(vC_hi, v1_hi), XOR(vC_lo, v1_lo)
            z = vB_lo % 2^32 + vC_lo % 2^32
            vB_lo = z % 2^32
            vB_hi = vB_hi + vC_hi + (z - vB_lo) / 2^32
            v6_lo, v6_hi = XOR(v6_lo, vB_lo), XOR(v6_hi, vB_hi)
            z_lo, z_hi = v6_lo % 2^24, v6_hi % 2^24
            v6_lo, v6_hi = (v6_lo - z_lo) / 2^24 % 2^8 + z_hi * 2^8, (v6_hi - z_hi) / 2^24 % 2^8 + z_lo * 2^8
            k = row[12] * 2
            z = v1_lo % 2^32 + v6_lo % 2^32 + W[k-1]
            v1_lo = z % 2^32
            v1_hi = v1_hi + v6_hi + (z - v1_lo) / 2^32 + W[k]
            vC_lo, vC_hi = XOR(vC_lo, v1_lo), XOR(vC_hi, v1_hi)
            z_lo, z_hi = vC_lo % 2^16, vC_hi % 2^16
            vC_lo, vC_hi = (vC_lo - z_lo) / 2^16 % 2^16 + z_hi * 2^16, (vC_hi - z_hi) / 2^16 % 2^16 + z_lo * 2^16
            z = vB_lo % 2^32 + vC_lo % 2^32
            vB_lo = z % 2^32
            vB_hi = vB_hi + vC_hi + (z - vB_lo) / 2^32
            v6_lo, v6_hi = XOR(v6_lo, vB_lo), XOR(v6_hi, vB_hi)
            z_lo, z_hi = v6_lo % 2^31, v6_hi % 2^31
            v6_lo, v6_hi = z_lo * 2^1 + (v6_hi - z_hi) / 2^31 % 2^1, z_hi * 2^1 + (v6_lo - z_lo) / 2^31 % 2^1
            k = row[13] * 2
            z = v2_lo % 2^32 + v7_lo % 2^32 + W[k-1]
            v2_lo = z % 2^32
            v2_hi = v2_hi + v7_hi + (z - v2_lo) / 2^32 + W[k]
            vD_lo, vD_hi = XOR(vD_hi, v2_hi), XOR(vD_lo, v2_lo)
            z = v8_lo % 2^32 + vD_lo % 2^32
            v8_lo = z % 2^32
            v8_hi = v8_hi + vD_hi + (z - v8_lo) / 2^32
            v7_lo, v7_hi = XOR(v7_lo, v8_lo), XOR(v7_hi, v8_hi)
            z_lo, z_hi = v7_lo % 2^24, v7_hi % 2^24
            v7_lo, v7_hi = (v7_lo - z_lo) / 2^24 % 2^8 + z_hi * 2^8, (v7_hi - z_hi) / 2^24 % 2^8 + z_lo * 2^8
            k = row[14] * 2
            z = v2_lo % 2^32 + v7_lo % 2^32 + W[k-1]
            v2_lo = z % 2^32
            v2_hi = v2_hi + v7_hi + (z - v2_lo) / 2^32 + W[k]
            vD_lo, vD_hi = XOR(vD_lo, v2_lo), XOR(vD_hi, v2_hi)
            z_lo, z_hi = vD_lo % 2^16, vD_hi % 2^16
            vD_lo, vD_hi = (vD_lo - z_lo) / 2^16 % 2^16 + z_hi * 2^16, (vD_hi - z_hi) / 2^16 % 2^16 + z_lo * 2^16
            z = v8_lo % 2^32 + vD_lo % 2^32
            v8_lo = z % 2^32
            v8_hi = v8_hi + vD_hi + (z - v8_lo) / 2^32
            v7_lo, v7_hi = XOR(v7_lo, v8_lo), XOR(v7_hi, v8_hi)
            z_lo, z_hi = v7_lo % 2^31, v7_hi % 2^31
            v7_lo, v7_hi = z_lo * 2^1 + (v7_hi - z_hi) / 2^31 % 2^1, z_hi * 2^1 + (v7_lo - z_lo) / 2^31 % 2^1
            k = row[15] * 2
            z = v3_lo % 2^32 + v4_lo % 2^32 + W[k-1]
            v3_lo = z % 2^32
            v3_hi = v3_hi + v4_hi + (z - v3_lo) / 2^32 + W[k]
            vE_lo, vE_hi = XOR(vE_hi, v3_hi), XOR(vE_lo, v3_lo)
            z = v9_lo % 2^32 + vE_lo % 2^32
            v9_lo = z % 2^32
            v9_hi = v9_hi + vE_hi + (z - v9_lo) / 2^32
            v4_lo, v4_hi = XOR(v4_lo, v9_lo), XOR(v4_hi, v9_hi)
            z_lo, z_hi = v4_lo % 2^24, v4_hi % 2^24
            v4_lo, v4_hi = (v4_lo - z_lo) / 2^24 % 2^8 + z_hi * 2^8, (v4_hi - z_hi) / 2^24 % 2^8 + z_lo * 2^8
            k = row[16] * 2
            z = v3_lo % 2^32 + v4_lo % 2^32 + W[k-1]
            v3_lo = z % 2^32
            v3_hi = v3_hi + v4_hi + (z - v3_lo) / 2^32 + W[k]
            vE_lo, vE_hi = XOR(vE_lo, v3_lo), XOR(vE_hi, v3_hi)
            z_lo, z_hi = vE_lo % 2^16, vE_hi % 2^16
            vE_lo, vE_hi = (vE_lo - z_lo) / 2^16 % 2^16 + z_hi * 2^16, (vE_hi - z_hi) / 2^16 % 2^16 + z_lo * 2^16
            z = v9_lo % 2^32 + vE_lo % 2^32
            v9_lo = z % 2^32
            v9_hi = v9_hi + vE_hi + (z - v9_lo) / 2^32
            v4_lo, v4_hi = XOR(v4_lo, v9_lo), XOR(v4_hi, v9_hi)
            z_lo, z_hi = v4_lo % 2^31, v4_hi % 2^31
            v4_lo, v4_hi = z_lo * 2^1 + (v4_hi - z_hi) / 2^31 % 2^1, z_hi * 2^1 + (v4_lo - z_lo) / 2^31 % 2^1
         end
         h1_lo = XOR(h1_lo, v0_lo, v8_lo) % 2^32
         h2_lo = XOR(h2_lo, v1_lo, v9_lo) % 2^32
         h3_lo = XOR(h3_lo, v2_lo, vA_lo) % 2^32
         h4_lo = XOR(h4_lo, v3_lo, vB_lo) % 2^32
         h5_lo = XOR(h5_lo, v4_lo, vC_lo) % 2^32
         h6_lo = XOR(h6_lo, v5_lo, vD_lo) % 2^32
         h7_lo = XOR(h7_lo, v6_lo, vE_lo) % 2^32
         h8_lo = XOR(h8_lo, v7_lo, vF_lo) % 2^32
         h1_hi = XOR(h1_hi, v0_hi, v8_hi) % 2^32
         h2_hi = XOR(h2_hi, v1_hi, v9_hi) % 2^32
         h3_hi = XOR(h3_hi, v2_hi, vA_hi) % 2^32
         h4_hi = XOR(h4_hi, v3_hi, vB_hi) % 2^32
         h5_hi = XOR(h5_hi, v4_hi, vC_hi) % 2^32
         h6_hi = XOR(h6_hi, v5_hi, vD_hi) % 2^32
         h7_hi = XOR(h7_hi, v6_hi, vE_hi) % 2^32
         h8_hi = XOR(h8_hi, v7_hi, vF_hi) % 2^32
      end
      H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8] = h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo
      H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8] = h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi
      return bytes_compressed
   end


   function blake3_feed_64(str, offs, size, flags, chunk_index, H_in, H_out, wide_output, block_length)
      -- offs >= 0, size >= 0, size is multiple of 64
      block_length = block_length or 64
      local W = common_W
      local h1, h2, h3, h4, h5, h6, h7, h8 = H_in[1], H_in[2], H_in[3], H_in[4], H_in[5], H_in[6], H_in[7], H_in[8]
      H_out = H_out or H_in
      for pos = offs, offs + size - 1, 64 do
         if str then
            for j = 1, 16 do
               pos = pos + 4
               local a, b, c, d = byte(str, pos - 3, pos)
               W[j] = ((d * 256 + c) * 256 + b) * 256 + a
            end
         end
         local v0, v1, v2, v3, v4, v5, v6, v7 = h1, h2, h3, h4, h5, h6, h7, h8
         local v8, v9, vA, vB = sha2_H_hi[1], sha2_H_hi[2], sha2_H_hi[3], sha2_H_hi[4]
         local vC = chunk_index % 2^32         -- t0 = low_4_bytes(chunk_index)
         local vD = (chunk_index - vC) / 2^32  -- t1 = high_4_bytes(chunk_index)
         local vE, vF = block_length, flags
         for j = 1, 7 do
            v0 = v0 + v4 + W[perm_blake3[j]]
            vC = XOR(vC, v0) % 2^32 / 2^16
            vC = vC % 1 * (2^32 - 1) + vC
            v8 = v8 + vC
            v4 = XOR(v4, v8) % 2^32 / 2^12
            v4 = v4 % 1 * (2^32 - 1) + v4
            v0 = v0 + v4 + W[perm_blake3[j + 14]]
            vC = XOR(vC, v0) % 2^32 / 2^8
            vC = vC % 1 * (2^32 - 1) + vC
            v8 = v8 + vC
            v4 = XOR(v4, v8) % 2^32 / 2^7
            v4 = v4 % 1 * (2^32 - 1) + v4
            v1 = v1 + v5 + W[perm_blake3[j + 1]]
            vD = XOR(vD, v1) % 2^32 / 2^16
            vD = vD % 1 * (2^32 - 1) + vD
            v9 = v9 + vD
            v5 = XOR(v5, v9) % 2^32 / 2^12
            v5 = v5 % 1 * (2^32 - 1) + v5
            v1 = v1 + v5 + W[perm_blake3[j + 2]]
            vD = XOR(vD, v1) % 2^32 / 2^8
            vD = vD % 1 * (2^32 - 1) + vD
            v9 = v9 + vD
            v5 = XOR(v5, v9) % 2^32 / 2^7
            v5 = v5 % 1 * (2^32 - 1) + v5
            v2 = v2 + v6 + W[perm_blake3[j + 16]]
            vE = XOR(vE, v2) % 2^32 / 2^16
            vE = vE % 1 * (2^32 - 1) + vE
            vA = vA + vE
            v6 = XOR(v6, vA) % 2^32 / 2^12
            v6 = v6 % 1 * (2^32 - 1) + v6
            v2 = v2 + v6 + W[perm_blake3[j + 7]]
            vE = XOR(vE, v2) % 2^32 / 2^8
            vE = vE % 1 * (2^32 - 1) + vE
            vA = vA + vE
            v6 = XOR(v6, vA) % 2^32 / 2^7
            v6 = v6 % 1 * (2^32 - 1) + v6
            v3 = v3 + v7 + W[perm_blake3[j + 15]]
            vF = XOR(vF, v3) % 2^32 / 2^16
            vF = vF % 1 * (2^32 - 1) + vF
            vB = vB + vF
            v7 = XOR(v7, vB) % 2^32 / 2^12
            v7 = v7 % 1 * (2^32 - 1) + v7
            v3 = v3 + v7 + W[perm_blake3[j + 17]]
            vF = XOR(vF, v3) % 2^32 / 2^8
            vF = vF % 1 * (2^32 - 1) + vF
            vB = vB + vF
            v7 = XOR(v7, vB) % 2^32 / 2^7
            v7 = v7 % 1 * (2^32 - 1) + v7
            v0 = v0 + v5 + W[perm_blake3[j + 21]]
            vF = XOR(vF, v0) % 2^32 / 2^16
            vF = vF % 1 * (2^32 - 1) + vF
            vA = vA + vF
            v5 = XOR(v5, vA) % 2^32 / 2^12
            v5 = v5 % 1 * (2^32 - 1) + v5
            v0 = v0 + v5 + W[perm_blake3[j + 5]]
            vF = XOR(vF, v0) % 2^32 / 2^8
            vF = vF % 1 * (2^32 - 1) + vF
            vA = vA + vF
            v5 = XOR(v5, vA) % 2^32 / 2^7
            v5 = v5 % 1 * (2^32 - 1) + v5
            v1 = v1 + v6 + W[perm_blake3[j + 3]]
            vC = XOR(vC, v1) % 2^32 / 2^16
            vC = vC % 1 * (2^32 - 1) + vC
            vB = vB + vC
            v6 = XOR(v6, vB) % 2^32 / 2^12
            v6 = v6 % 1 * (2^32 - 1) + v6
            v1 = v1 + v6 + W[perm_blake3[j + 6]]
            vC = XOR(vC, v1) % 2^32 / 2^8
            vC = vC % 1 * (2^32 - 1) + vC
            vB = vB + vC
            v6 = XOR(v6, vB) % 2^32 / 2^7
            v6 = v6 % 1 * (2^32 - 1) + v6
            v2 = v2 + v7 + W[perm_blake3[j + 4]]
            vD = XOR(vD, v2) % 2^32 / 2^16
            vD = vD % 1 * (2^32 - 1) + vD
            v8 = v8 + vD
            v7 = XOR(v7, v8) % 2^32 / 2^12
            v7 = v7 % 1 * (2^32 - 1) + v7
            v2 = v2 + v7 + W[perm_blake3[j + 18]]
            vD = XOR(vD, v2) % 2^32 / 2^8
            vD = vD % 1 * (2^32 - 1) + vD
            v8 = v8 + vD
            v7 = XOR(v7, v8) % 2^32 / 2^7
            v7 = v7 % 1 * (2^32 - 1) + v7
            v3 = v3 + v4 + W[perm_blake3[j + 19]]
            vE = XOR(vE, v3) % 2^32 / 2^16
            vE = vE % 1 * (2^32 - 1) + vE
            v9 = v9 + vE
            v4 = XOR(v4, v9) % 2^32 / 2^12
            v4 = v4 % 1 * (2^32 - 1) + v4
            v3 = v3 + v4 + W[perm_blake3[j + 20]]
            vE = XOR(vE, v3) % 2^32 / 2^8
            vE = vE % 1 * (2^32 - 1) + vE
            v9 = v9 + vE
            v4 = XOR(v4, v9) % 2^32 / 2^7
            v4 = v4 % 1 * (2^32 - 1) + v4
         end
         if wide_output then
            H_out[ 9] = XOR(h1, v8)
            H_out[10] = XOR(h2, v9)
            H_out[11] = XOR(h3, vA)
            H_out[12] = XOR(h4, vB)
            H_out[13] = XOR(h5, vC)
            H_out[14] = XOR(h6, vD)
            H_out[15] = XOR(h7, vE)
            H_out[16] = XOR(h8, vF)
         end
         h1 = XOR(v0, v8)
         h2 = XOR(v1, v9)
         h3 = XOR(v2, vA)
         h4 = XOR(v3, vB)
         h5 = XOR(v4, vC)
         h6 = XOR(v5, vD)
         h7 = XOR(v6, vE)
         h8 = XOR(v7, vF)
      end
      H_out[1], H_out[2], H_out[3], H_out[4], H_out[5], H_out[6], H_out[7], H_out[8] = h1, h2, h3, h4, h5, h6, h7, h8
   end

end


--------------------------------------------------------------------------------
-- MAGIC NUMBERS CALCULATOR
--------------------------------------------------------------------------------
-- Q:
--    Is 53-bit "double" math enough to calculate square roots and cube roots of primes with 64 correct bits after decimal point?
-- A:
--    Yes, 53-bit "double" arithmetic is enough.
--    We could obtain first 40 bits by direct calculation of p^(1/3) and next 40 bits by one step of Newton's method.

do
   local function mul(src1, src2, factor, result_length)
      -- src1, src2 - long integers (arrays of digits in base 2^24)
      -- factor - small integer
      -- returns long integer result (src1 * src2 * factor) and its floating point approximation
      local result, carry, value, weight = {}, 0.0, 0.0, 1.0
      for j = 1, result_length do
         for k = math_max(1, j + 1 - #src2), math_min(j, #src1) do
            carry = carry + factor * src1[k] * src2[j + 1 - k]  -- "int32" is not enough for multiplication result, that's why "factor" must be of type "double"
         end
         local digit = carry % 2^24
         result[j] = floor(digit)
         carry = (carry - digit) / 2^24
         value = value + digit * weight
         weight = weight * 2^24
      end
      return result, value
   end

   local idx, step, p, one, sqrt_hi, sqrt_lo = 0, {4, 1, 2, -2, 2}, 4, {1}, sha2_H_hi, sha2_H_lo
   repeat
      p = p + step[p % 6]
      local d = 1
      repeat
         d = d + step[d % 6]
         if d*d > p then -- next prime number is found
            local root = p^(1/3)
            local R = root * 2^40
            R = mul({R - R % 1}, one, 1.0, 2)
            local _, delta = mul(R, mul(R, R, 1.0, 4), -1.0, 4)
            local hi = R[2] % 65536 * 65536 + floor(R[1] / 256)
            local lo = R[1] % 256 * 16777216 + floor(delta * (2^-56 / 3) * root / p)
            if idx < 16 then
               root = p^(1/2)
               R = root * 2^40
               R = mul({R - R % 1}, one, 1.0, 2)
               _, delta = mul(R, R, -1.0, 2)
               local hi = R[2] % 65536 * 65536 + floor(R[1] / 256)
               local lo = R[1] % 256 * 16777216 + floor(delta * 2^-17 / root)
               local idx = idx % 8 + 1
               sha2_H_ext256[224][idx] = lo
               sqrt_hi[idx], sqrt_lo[idx] = hi, lo + hi * hi_factor
               if idx > 7 then
                  sqrt_hi, sqrt_lo = sha2_H_ext512_hi[384], sha2_H_ext512_lo[384]
               end
            end
            idx = idx + 1
            sha2_K_hi[idx], sha2_K_lo[idx] = hi, lo % K_lo_modulo + hi * hi_factor
            break
         end
      until p % d == 0
   until idx > 79
end

-- Calculating IVs for SHA512/224 and SHA512/256
for width = 224, 256, 32 do
   local H_lo, H_hi = {}
   if HEX64 then
      for j = 1, 8 do
         H_lo[j] = XORA5(sha2_H_lo[j])
      end
   else
      H_hi = {}
      for j = 1, 8 do
         H_lo[j] = XORA5(sha2_H_lo[j])
         H_hi[j] = XORA5(sha2_H_hi[j])
      end
   end
   sha512_feed_128(H_lo, H_hi, "SHA-512/"..tostring(width).."\128"..string_rep("\0", 115).."\88", 0, 128)
   sha2_H_ext512_lo[width] = H_lo
   sha2_H_ext512_hi[width] = H_hi
end

-- Constants for MD5
do
   local sin, abs, modf = math.sin, math.abs, math.modf
   for idx = 1, 64 do
      -- we can't use formula floor(abs(sin(idx))*2^32) because its result may be beyond integer range on Lua built with 32-bit integers
      local hi, lo = modf(abs(sin(idx)) * 2^16)
      md5_K[idx] = hi * 65536 + floor(lo * 2^16)
   end
end

-- Constants for SHA-3
do
   local sh_reg = 29

   local function next_bit()
      local r = sh_reg % 2
      sh_reg = XOR_BYTE((sh_reg - r) / 2, 142 * r)
      return r
   end

   for idx = 1, 24 do
      local lo, m = 0
      for _ = 1, 6 do
         m = m and m * m * 2 or 1
         lo = lo + next_bit() * m
      end
      local hi = next_bit() * m
      sha3_RC_hi[idx], sha3_RC_lo[idx] = hi, lo + hi * hi_factor_keccak
   end
end

if branch == "FFI" then
   sha2_K_hi = ffi.new("uint32_t[?]", #sha2_K_hi + 1, 0, unpack(sha2_K_hi))
   sha2_K_lo = ffi.new("int64_t[?]",  #sha2_K_lo + 1, 0, unpack(sha2_K_lo))
   --md5_K = ffi.new("uint32_t[?]", #md5_K + 1, 0, unpack(md5_K))
   if hi_factor_keccak == 0 then
      sha3_RC_lo = ffi.new("uint32_t[?]", #sha3_RC_lo + 1, 0, unpack(sha3_RC_lo))
      sha3_RC_hi = ffi.new("uint32_t[?]", #sha3_RC_hi + 1, 0, unpack(sha3_RC_hi))
   else
      sha3_RC_lo = ffi.new("int64_t[?]", #sha3_RC_lo + 1, 0, unpack(sha3_RC_lo))
   end
end


--------------------------------------------------------------------------------
-- MAIN FUNCTIONS
--------------------------------------------------------------------------------

local function sha256ext(width, message)
   -- Create an instance (private objects for current calculation)
   local H, length, tail = {unpack(sha2_H_ext256[width])}, 0.0, ""

   local function partial(message_part)
      if message_part then
         if tail then
            length = length + #message_part
            local offs = 0
            if tail ~= "" and #tail + #message_part >= 64 then
               offs = 64 - #tail
               sha256_feed_64(H, tail..sub(message_part, 1, offs), 0, 64)
               tail = ""
            end
            local size = #message_part - offs
            local size_tail = size % 64
            sha256_feed_64(H, message_part, offs, size - size_tail)
            tail = tail..sub(message_part, #message_part + 1 - size_tail)
            return partial
         else
            error("Adding more chunks is not allowed after receiving the result", 2)
         end
      else
         if tail then
            local final_blocks = {tail, "\128", string_rep("\0", (-9 - length) % 64 + 1)}
            tail = nil
            -- Assuming user data length is shorter than (2^53)-9 bytes
            -- Anyway, it looks very unrealistic that someone would spend more than a year of calculations to process 2^53 bytes of data by using this Lua script :-)
            -- 2^53 bytes = 2^56 bits, so "bit-counter" fits in 7 bytes
            length = length * (8 / 256^7)  -- convert "byte-counter" to "bit-counter" and move decimal point to the left
            for j = 4, 10 do
               length = length % 1 * 256
               final_blocks[j] = char(floor(length))
            end
            final_blocks = table_concat(final_blocks)
            sha256_feed_64(H, final_blocks, 0, #final_blocks)
            local max_reg = width / 32
            for j = 1, max_reg do
               H[j] = HEX(H[j])
            end
            H = table_concat(H, "", 1, max_reg)
         end
         return H
      end
   end

   if message then
      -- Actually perform calculations and return the SHA256 digest of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading
      -- User should feed every chunk of input data as single argument to this function and finally get SHA256 digest by invoking this function without an argument
      return partial
   end
end


local function sha512ext(width, message)
   -- Create an instance (private objects for current calculation)
   local length, tail, H_lo, H_hi = 0.0, "", {unpack(sha2_H_ext512_lo[width])}, not HEX64 and {unpack(sha2_H_ext512_hi[width])}

   local function partial(message_part)
      if message_part then
         if tail then
            length = length + #message_part
            local offs = 0
            if tail ~= "" and #tail + #message_part >= 128 then
               offs = 128 - #tail
               sha512_feed_128(H_lo, H_hi, tail..sub(message_part, 1, offs), 0, 128)
               tail = ""
            end
            local size = #message_part - offs
            local size_tail = size % 128
            sha512_feed_128(H_lo, H_hi, message_part, offs, size - size_tail)
            tail = tail..sub(message_part, #message_part + 1 - size_tail)
            return partial
         else
            error("Adding more chunks is not allowed after receiving the result", 2)
         end
      else
         if tail then
            local final_blocks = {tail, "\128", string_rep("\0", (-17-length) % 128 + 9)}
            tail = nil
            -- Assuming user data length is shorter than (2^53)-17 bytes
            -- 2^53 bytes = 2^56 bits, so "bit-counter" fits in 7 bytes
            length = length * (8 / 256^7)  -- convert "byte-counter" to "bit-counter" and move floating point to the left
            for j = 4, 10 do
               length = length % 1 * 256
               final_blocks[j] = char(floor(length))
            end
            final_blocks = table_concat(final_blocks)
            sha512_feed_128(H_lo, H_hi, final_blocks, 0, #final_blocks)
            local max_reg = ceil(width / 64)
            if HEX64 then
               for j = 1, max_reg do
                  H_lo[j] = HEX64(H_lo[j])
               end
            else
               for j = 1, max_reg do
                  H_lo[j] = HEX(H_hi[j])..HEX(H_lo[j])
               end
               H_hi = nil
            end
            H_lo = sub(table_concat(H_lo, "", 1, max_reg), 1, width / 4)
         end
         return H_lo
      end
   end

   if message then
      -- Actually perform calculations and return the SHA512 digest of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading
      -- User should feed every chunk of input data as single argument to this function and finally get SHA512 digest by invoking this function without an argument
      return partial
   end
end


local function md5(message)
   -- Create an instance (private objects for current calculation)
   local H, length, tail = {unpack(md5_sha1_H, 1, 4)}, 0.0, ""

   local function partial(message_part)
      if message_part then
         if tail then
            length = length + #message_part
            local offs = 0
            if tail ~= "" and #tail + #message_part >= 64 then
               offs = 64 - #tail
               md5_feed_64(H, tail..sub(message_part, 1, offs), 0, 64)
               tail = ""
            end
            local size = #message_part - offs
            local size_tail = size % 64
            md5_feed_64(H, message_part, offs, size - size_tail)
            tail = tail..sub(message_part, #message_part + 1 - size_tail)
            return partial
         else
            error("Adding more chunks is not allowed after receiving the result", 2)
         end
      else
         if tail then
            local final_blocks = {tail, "\128", string_rep("\0", (-9 - length) % 64)}
            tail = nil
            length = length * 8  -- convert "byte-counter" to "bit-counter"
            for j = 4, 11 do
               local low_byte = length % 256
               final_blocks[j] = char(low_byte)
               length = (length - low_byte) / 256
            end
            final_blocks = table_concat(final_blocks)
            md5_feed_64(H, final_blocks, 0, #final_blocks)
            for j = 1, 4 do
               H[j] = HEX(H[j])
            end
            H = gsub(table_concat(H), "(..)(..)(..)(..)", "%4%3%2%1")
         end
         return H
      end
   end

   if message then
      -- Actually perform calculations and return the MD5 digest of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading
      -- User should feed every chunk of input data as single argument to this function and finally get MD5 digest by invoking this function without an argument
      return partial
   end
end


local function sha1(message)
   -- Create an instance (private objects for current calculation)
   local H, length, tail = {unpack(md5_sha1_H)}, 0.0, ""

   local function partial(message_part)
      if message_part then
         if tail then
            length = length + #message_part
            local offs = 0
            if tail ~= "" and #tail + #message_part >= 64 then
               offs = 64 - #tail
               sha1_feed_64(H, tail..sub(message_part, 1, offs), 0, 64)
               tail = ""
            end
            local size = #message_part - offs
            local size_tail = size % 64
            sha1_feed_64(H, message_part, offs, size - size_tail)
            tail = tail..sub(message_part, #message_part + 1 - size_tail)
            return partial
         else
            error("Adding more chunks is not allowed after receiving the result", 2)
         end
      else
         if tail then
            local final_blocks = {tail, "\128", string_rep("\0", (-9 - length) % 64 + 1)}
            tail = nil
            -- Assuming user data length is shorter than (2^53)-9 bytes
            -- 2^53 bytes = 2^56 bits, so "bit-counter" fits in 7 bytes
            length = length * (8 / 256^7)  -- convert "byte-counter" to "bit-counter" and move decimal point to the left
            for j = 4, 10 do
               length = length % 1 * 256
               final_blocks[j] = char(floor(length))
            end
            final_blocks = table_concat(final_blocks)
            sha1_feed_64(H, final_blocks, 0, #final_blocks)
            for j = 1, 5 do
               H[j] = HEX(H[j])
            end
            H = table_concat(H)
         end
         return H
      end
   end

   if message then
      -- Actually perform calculations and return the SHA-1 digest of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading
      -- User should feed every chunk of input data as single argument to this function and finally get SHA-1 digest by invoking this function without an argument
      return partial
   end
end


local function keccak(block_size_in_bytes, digest_size_in_bytes, is_SHAKE, message)
   -- "block_size_in_bytes" is multiple of 8
   if type(digest_size_in_bytes) ~= "number" then
      -- arguments in SHAKE are swapped:
      --    NIST FIPS 202 defines SHAKE(message,num_bits)
      --    this module   defines SHAKE(num_bytes,message)
      -- it's easy to forget about this swap, hence the check
      error("Argument 'digest_size_in_bytes' must be a number", 2)
   end
   -- Create an instance (private objects for current calculation)
   local tail, lanes_lo, lanes_hi = "", create_array_of_lanes(), hi_factor_keccak == 0 and create_array_of_lanes()
   local result

   local function partial(message_part)
      if message_part then
         if tail then
            local offs = 0
            if tail ~= "" and #tail + #message_part >= block_size_in_bytes then
               offs = block_size_in_bytes - #tail
               keccak_feed(lanes_lo, lanes_hi, tail..sub(message_part, 1, offs), 0, block_size_in_bytes, block_size_in_bytes)
               tail = ""
            end
            local size = #message_part - offs
            local size_tail = size % block_size_in_bytes
            keccak_feed(lanes_lo, lanes_hi, message_part, offs, size - size_tail, block_size_in_bytes)
            tail = tail..sub(message_part, #message_part + 1 - size_tail)
            return partial
         else
            error("Adding more chunks is not allowed after receiving the result", 2)
         end
      else
         if tail then
            -- append the following bits to the message: for usual SHA-3: 011(0*)1, for SHAKE: 11111(0*)1
            local gap_start = is_SHAKE and 31 or 6
            tail = tail..(#tail + 1 == block_size_in_bytes and char(gap_start + 128) or char(gap_start)..string_rep("\0", (-2 - #tail) % block_size_in_bytes).."\128")
            keccak_feed(lanes_lo, lanes_hi, tail, 0, #tail, block_size_in_bytes)
            tail = nil
            local lanes_used = 0
            local total_lanes = floor(block_size_in_bytes / 8)
            local qwords = {}

            local function get_next_qwords_of_digest(qwords_qty)
               -- returns not more than 'qwords_qty' qwords ('qwords_qty' might be non-integer)
               -- doesn't go across keccak-buffer boundary
               -- block_size_in_bytes is a multiple of 8, so, keccak-buffer contains integer number of qwords
               if lanes_used >= total_lanes then
                  keccak_feed(lanes_lo, lanes_hi, "\0\0\0\0\0\0\0\0", 0, 8, 8)
                  lanes_used = 0
               end
               qwords_qty = floor(math_min(qwords_qty, total_lanes - lanes_used))
               if hi_factor_keccak ~= 0 then
                  for j = 1, qwords_qty do
                     qwords[j] = HEX64(lanes_lo[lanes_used + j - 1 + lanes_index_base])
                  end
               else
                  for j = 1, qwords_qty do
                     qwords[j] = HEX(lanes_hi[lanes_used + j])..HEX(lanes_lo[lanes_used + j])
                  end
               end
               lanes_used = lanes_used + qwords_qty
               return
                  gsub(table_concat(qwords, "", 1, qwords_qty), "(..)(..)(..)(..)(..)(..)(..)(..)", "%8%7%6%5%4%3%2%1"),
                  qwords_qty * 8
            end

            local parts = {}      -- digest parts
            local last_part, last_part_size = "", 0

            local function get_next_part_of_digest(bytes_needed)
               -- returns 'bytes_needed' bytes, for arbitrary integer 'bytes_needed'
               bytes_needed = bytes_needed or 1
               if bytes_needed <= last_part_size then
                  last_part_size = last_part_size - bytes_needed
                  local part_size_in_nibbles = bytes_needed * 2
                  local result = sub(last_part, 1, part_size_in_nibbles)
                  last_part = sub(last_part, part_size_in_nibbles + 1)
                  return result
               end
               local parts_qty = 0
               if last_part_size > 0 then
                  parts_qty = 1
                  parts[parts_qty] = last_part
                  bytes_needed = bytes_needed - last_part_size
               end
               -- repeats until the length is enough
               while bytes_needed >= 8 do
                  local next_part, next_part_size = get_next_qwords_of_digest(bytes_needed / 8)
                  parts_qty = parts_qty + 1
                  parts[parts_qty] = next_part
                  bytes_needed = bytes_needed - next_part_size
               end
               if bytes_needed > 0 then
                  last_part, last_part_size = get_next_qwords_of_digest(1)
                  parts_qty = parts_qty + 1
                  parts[parts_qty] = get_next_part_of_digest(bytes_needed)
               else
                  last_part, last_part_size = "", 0
               end
               return table_concat(parts, "", 1, parts_qty)
            end

            if digest_size_in_bytes < 0 then
               result = get_next_part_of_digest
            else
               result = get_next_part_of_digest(digest_size_in_bytes)
            end
         end
         return result
      end
   end

   if message then
      -- Actually perform calculations and return the SHA-3 digest of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading
      -- User should feed every chunk of input data as single argument to this function and finally get SHA-3 digest by invoking this function without an argument
      return partial
   end
end


local hex_to_bin, bin_to_hex, bin_to_base64, base64_to_bin
do
   function hex_to_bin(hex_string)
      return (gsub(hex_string, "%x%x",
         function (hh)
            return char(tonumber(hh, 16))
         end
      ))
   end

   function bin_to_hex(binary_string)
      return (gsub(binary_string, ".",
         function (c)
            return string_format("%02x", byte(c))
         end
      ))
   end

   local base64_symbols = {
      ['+'] = 62, ['-'] = 62,  [62] = '+',
      ['/'] = 63, ['_'] = 63,  [63] = '/',
      ['='] = -1, ['.'] = -1,  [-1] = '='
   }
   local symbol_index = 0
   for j, pair in ipairs{'AZ', 'az', '09'} do
      for ascii = byte(pair), byte(pair, 2) do
         local ch = char(ascii)
         base64_symbols[ch] = symbol_index
         base64_symbols[symbol_index] = ch
         symbol_index = symbol_index + 1
      end
   end

   function bin_to_base64(binary_string)
      local result = {}
      for pos = 1, #binary_string, 3 do
         local c1, c2, c3, c4 = byte(sub(binary_string, pos, pos + 2)..'\0', 1, -1)
         result[#result + 1] =
            base64_symbols[floor(c1 / 4)]
            ..base64_symbols[c1 % 4 * 16 + floor(c2 / 16)]
            ..base64_symbols[c3 and c2 % 16 * 4 + floor(c3 / 64) or -1]
            ..base64_symbols[c4 and c3 % 64 or -1]
      end
      return table_concat(result)
   end

   function base64_to_bin(base64_string)
      local result, chars_qty = {}, 3
      for pos, ch in gmatch(gsub(base64_string, '%s+', ''), '()(.)') do
         local code = base64_symbols[ch]
         if code < 0 then
            chars_qty = chars_qty - 1
            code = 0
         end
         local idx = pos % 4
         if idx > 0 then
            result[-idx] = code
         else
            local c1 = result[-1] * 4 + floor(result[-2] / 16)
            local c2 = (result[-2] % 16) * 16 + floor(result[-3] / 4)
            local c3 = (result[-3] % 4) * 64 + code
            result[#result + 1] = sub(char(c1, c2, c3), 1, chars_qty)
         end
      end
      return table_concat(result)
   end

end


local block_size_for_HMAC  -- this table will be initialized at the end of the module

local function pad_and_xor(str, result_length, byte_for_xor)
   return gsub(str, ".",
      function(c)
         return char(XOR_BYTE(byte(c), byte_for_xor))
      end
   )..string_rep(char(byte_for_xor), result_length - #str)
end

local function hmac(hash_func, key, message)
   -- Create an instance (private objects for current calculation)
   local block_size = block_size_for_HMAC[hash_func]
   if not block_size then
      error("Unknown hash function", 2)
   end
   if #key > block_size then
      key = hex_to_bin(hash_func(key))
   end
   local append = hash_func()(pad_and_xor(key, block_size, 0x36))
   local result

   local function partial(message_part)
      if not message_part then
         result = result or hash_func(pad_and_xor(key, block_size, 0x5C)..hex_to_bin(append()))
         return result
      elseif result then
         error("Adding more chunks is not allowed after receiving the result", 2)
      else
         append(message_part)
         return partial
      end
   end

   if message then
      -- Actually perform calculations and return the HMAC of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading of a message
      -- User should feed every chunk of the message as single argument to this function and finally get HMAC by invoking this function without an argument
      return partial
   end
end


local function xor_blake2_salt(salt, letter, H_lo, H_hi)
   -- salt: concatenation of "Salt"+"Personalization" fields
   local max_size = letter == "s" and 16 or 32
   local salt_size = #salt
   if salt_size > max_size then
      error(string_format("For BLAKE2%s/BLAKE2%sp/BLAKE2X%s the 'salt' parameter length must not exceed %d bytes", letter, letter, letter, max_size), 2)
   end
   if H_lo then
      local offset, blake2_word_size, xor = 0, letter == "s" and 4 or 8, letter == "s" and XOR or XORA5
      for j = 5, 4 + ceil(salt_size / blake2_word_size) do
         local prev, last
         for _ = 1, blake2_word_size, 4 do
            offset = offset + 4
            local a, b, c, d = byte(salt, offset - 3, offset)
            local four_bytes = (((d or 0) * 256 + (c or 0)) * 256 + (b or 0)) * 256 + (a or 0)
            prev, last = last, four_bytes
         end
         H_lo[j] = xor(H_lo[j], prev and last * hi_factor + prev or last)
         if H_hi then
            H_hi[j] = xor(H_hi[j], last)
         end
      end
   end
end

local function blake2s(message, key, salt, digest_size_in_bytes, XOF_length, B2_offset)
   -- message:  binary string to be hashed (or nil for "chunk-by-chunk" input mode)
   -- key:      (optional) binary string up to 32 bytes, by default empty string
   -- salt:     (optional) binary string up to 16 bytes, by default empty string
   -- digest_size_in_bytes: (optional) integer from 1 to 32, by default 32
   -- The last two parameters "XOF_length" and "B2_offset" are for internal use only, user must omit them (or pass nil)
   digest_size_in_bytes = digest_size_in_bytes or 32
   if digest_size_in_bytes < 1 or digest_size_in_bytes > 32 then
      error("BLAKE2s digest length must be from 1 to 32 bytes", 2)
   end
   key = key or ""
   local key_length = #key
   if key_length > 32 then
      error("BLAKE2s key length must not exceed 32 bytes", 2)
   end
   salt = salt or ""
   local bytes_compressed, tail, H = 0.0, "", {unpack(sha2_H_hi)}
   if B2_offset then
      H[1] = XOR(H[1], digest_size_in_bytes)
      H[2] = XOR(H[2], 0x20)
      H[3] = XOR(H[3], B2_offset)
      H[4] = XOR(H[4], 0x20000000 + XOF_length)
   else
      H[1] = XOR(H[1], 0x01010000 + key_length * 256 + digest_size_in_bytes)
      if XOF_length then
         H[4] = XOR(H[4], XOF_length)
      end
   end
   if salt ~= "" then
      xor_blake2_salt(salt, "s", H)
   end

   local function partial(message_part)
      if message_part then
         if tail then
            local offs = 0
            if tail ~= "" and #tail + #message_part > 64 then
               offs = 64 - #tail
               bytes_compressed = blake2s_feed_64(H, tail..sub(message_part, 1, offs), 0, 64, bytes_compressed)
               tail = ""
            end
            local size = #message_part - offs
            local size_tail = size > 0 and (size - 1) % 64 + 1 or 0
            bytes_compressed = blake2s_feed_64(H, message_part, offs, size - size_tail, bytes_compressed)
            tail = tail..sub(message_part, #message_part + 1 - size_tail)
            return partial
         else
            error("Adding more chunks is not allowed after receiving the result", 2)
         end
      else
         if tail then
            if B2_offset then
               blake2s_feed_64(H, nil, 0, 64, 0, 32)
            else
               blake2s_feed_64(H, tail..string_rep("\0", 64 - #tail), 0, 64, bytes_compressed, #tail)
            end
            tail = nil
            if not XOF_length or B2_offset then
               local max_reg = ceil(digest_size_in_bytes / 4)
               for j = 1, max_reg do
                  H[j] = HEX(H[j])
               end
               H = sub(gsub(table_concat(H, "", 1, max_reg), "(..)(..)(..)(..)", "%4%3%2%1"), 1, digest_size_in_bytes * 2)
            end
         end
         return H
      end
   end

   if key_length > 0 then
      partial(key..string_rep("\0", 64 - key_length))
   end
   if B2_offset then
      return partial()
   elseif message then
      -- Actually perform calculations and return the BLAKE2s digest of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading
      -- User should feed every chunk of input data as single argument to this function and finally get BLAKE2s digest by invoking this function without an argument
      return partial
   end
end

local function blake2b(message, key, salt, digest_size_in_bytes, XOF_length, B2_offset)
   -- message:  binary string to be hashed (or nil for "chunk-by-chunk" input mode)
   -- key:      (optional) binary string up to 64 bytes, by default empty string
   -- salt:     (optional) binary string up to 32 bytes, by default empty string
   -- digest_size_in_bytes: (optional) integer from 1 to 64, by default 64
   -- The last two parameters "XOF_length" and "B2_offset" are for internal use only, user must omit them (or pass nil)
   digest_size_in_bytes = floor(digest_size_in_bytes or 64)
   if digest_size_in_bytes < 1 or digest_size_in_bytes > 64 then
      error("BLAKE2b digest length must be from 1 to 64 bytes", 2)
   end
   key = key or ""
   local key_length = #key
   if key_length > 64 then
      error("BLAKE2b key length must not exceed 64 bytes", 2)
   end
   salt = salt or ""
   local bytes_compressed, tail, H_lo, H_hi = 0.0, "", {unpack(sha2_H_lo)}, not HEX64 and {unpack(sha2_H_hi)}
   if B2_offset then
      if H_hi then
         H_lo[1] = XORA5(H_lo[1], digest_size_in_bytes)
         H_hi[1] = XORA5(H_hi[1], 0x40)
         H_lo[2] = XORA5(H_lo[2], B2_offset)
         H_hi[2] = XORA5(H_hi[2], XOF_length)
      else
         H_lo[1] = XORA5(H_lo[1], 0x40 * hi_factor + digest_size_in_bytes)
         H_lo[2] = XORA5(H_lo[2], XOF_length * hi_factor + B2_offset)
      end
      H_lo[3] = XORA5(H_lo[3], 0x4000)
   else
      H_lo[1] = XORA5(H_lo[1], 0x01010000 + key_length * 256 + digest_size_in_bytes)
      if XOF_length then
         if H_hi then
            H_hi[2] = XORA5(H_hi[2], XOF_length)
         else
            H_lo[2] = XORA5(H_lo[2], XOF_length * hi_factor)
         end
      end
   end
   if salt ~= "" then
      xor_blake2_salt(salt, "b", H_lo, H_hi)
   end

   local function partial(message_part)
      if message_part then
         if tail then
            local offs = 0
            if tail ~= "" and #tail + #message_part > 128 then
               offs = 128 - #tail
               bytes_compressed = blake2b_feed_128(H_lo, H_hi, tail..sub(message_part, 1, offs), 0, 128, bytes_compressed)
               tail = ""
            end
            local size = #message_part - offs
            local size_tail = size > 0 and (size - 1) % 128 + 1 or 0
            bytes_compressed = blake2b_feed_128(H_lo, H_hi, message_part, offs, size - size_tail, bytes_compressed)
            tail = tail..sub(message_part, #message_part + 1 - size_tail)
            return partial
         else
            error("Adding more chunks is not allowed after receiving the result", 2)
         end
      else
         if tail then
            if B2_offset then
               blake2b_feed_128(H_lo, H_hi, nil, 0, 128, 0, 64)
            else
               blake2b_feed_128(H_lo, H_hi, tail..string_rep("\0", 128 - #tail), 0, 128, bytes_compressed, #tail)
            end
            tail = nil
            if XOF_length and not B2_offset then
               if H_hi then
                  for j = 8, 1, -1 do
                     H_lo[j*2] = H_hi[j]
                     H_lo[j*2-1] = H_lo[j]
                  end
                  return H_lo, 16
               end
            else
               local max_reg = ceil(digest_size_in_bytes / 8)
               if H_hi then
                  for j = 1, max_reg do
                     H_lo[j] = HEX(H_hi[j])..HEX(H_lo[j])
                  end
               else
                  for j = 1, max_reg do
                     H_lo[j] = HEX64(H_lo[j])
                  end
               end
               H_lo = sub(gsub(table_concat(H_lo, "", 1, max_reg), "(..)(..)(..)(..)(..)(..)(..)(..)", "%8%7%6%5%4%3%2%1"), 1, digest_size_in_bytes * 2)
            end
            H_hi = nil
         end
         return H_lo
      end
   end

   if key_length > 0 then
      partial(key..string_rep("\0", 128 - key_length))
   end
   if B2_offset then
      return partial()
   elseif message then
      -- Actually perform calculations and return the BLAKE2b digest of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading
      -- User should feed every chunk of input data as single argument to this function and finally get BLAKE2b digest by invoking this function without an argument
      return partial
   end
end

local function blake2sp(message, key, salt, digest_size_in_bytes)
   -- message:  binary string to be hashed (or nil for "chunk-by-chunk" input mode)
   -- key:      (optional) binary string up to 32 bytes, by default empty string
   -- salt:     (optional) binary string up to 16 bytes, by default empty string
   -- digest_size_in_bytes: (optional) integer from 1 to 32, by default 32
   digest_size_in_bytes = digest_size_in_bytes or 32
   if digest_size_in_bytes < 1 or digest_size_in_bytes > 32 then
      error("BLAKE2sp digest length must be from 1 to 32 bytes", 2)
   end
   key = key or ""
   local key_length = #key
   if key_length > 32 then
      error("BLAKE2sp key length must not exceed 32 bytes", 2)
   end
   salt = salt or ""
   local instances, length, first_dword_of_parameter_block, result = {}, 0.0, 0x02080000 + key_length * 256 + digest_size_in_bytes
   for j = 1, 8 do
      local bytes_compressed, tail, H = 0.0, "", {unpack(sha2_H_hi)}
      instances[j] = {bytes_compressed, tail, H}
      H[1] = XOR(H[1], first_dword_of_parameter_block)
      H[3] = XOR(H[3], j-1)
      H[4] = XOR(H[4], 0x20000000)
      if salt ~= "" then
         xor_blake2_salt(salt, "s", H)
      end
   end

   local function partial(message_part)
      if message_part then
         if instances then
            local from = 0
            while true do
               local to = math_min(from + 64 - length % 64, #message_part)
               if to > from then
                  local inst = instances[floor(length / 64) % 8 + 1]
                  local part = sub(message_part, from + 1, to)
                  length, from = length + to - from, to
                  local bytes_compressed, tail = inst[1], inst[2]
                  if #tail < 64 then
                     tail = tail..part
                  else
                     local H = inst[3]
                     bytes_compressed = blake2s_feed_64(H, tail, 0, 64, bytes_compressed)
                     tail = part
                  end
                  inst[1], inst[2] = bytes_compressed, tail
               else
                  break
               end
            end
            return partial
         else
            error("Adding more chunks is not allowed after receiving the result", 2)
         end
      else
         if instances then
            local root_H = {unpack(sha2_H_hi)}
            root_H[1] = XOR(root_H[1], first_dword_of_parameter_block)
            root_H[4] = XOR(root_H[4], 0x20010000)
            if salt ~= "" then
               xor_blake2_salt(salt, "s", root_H)
            end
            for j = 1, 8 do
               local inst = instances[j]
               local bytes_compressed, tail, H = inst[1], inst[2], inst[3]
               blake2s_feed_64(H, tail..string_rep("\0", 64 - #tail), 0, 64, bytes_compressed, #tail, j == 8)
               if j % 2 == 0 then
                  local index = 0
                  for k = j - 1, j do
                     local inst = instances[k]
                     local H = inst[3]
                     for i = 1, 8 do
                        index = index + 1
                        common_W_blake2s[index] = H[i]
                     end
                  end
                  blake2s_feed_64(root_H, nil, 0, 64, 64 * (j/2 - 1), j == 8 and 64, j == 8)
               end
            end
            instances = nil
            local max_reg = ceil(digest_size_in_bytes / 4)
            for j = 1, max_reg do
               root_H[j] = HEX(root_H[j])
            end
            result = sub(gsub(table_concat(root_H, "", 1, max_reg), "(..)(..)(..)(..)", "%4%3%2%1"), 1, digest_size_in_bytes * 2)
         end
         return result
      end
   end

   if key_length > 0 then
      key = key..string_rep("\0", 64 - key_length)
      for j = 1, 8 do
         partial(key)
      end
   end
   if message then
      -- Actually perform calculations and return the BLAKE2sp digest of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading
      -- User should feed every chunk of input data as single argument to this function and finally get BLAKE2sp digest by invoking this function without an argument
      return partial
   end

end

local function blake2bp(message, key, salt, digest_size_in_bytes)
   -- message:  binary string to be hashed (or nil for "chunk-by-chunk" input mode)
   -- key:      (optional) binary string up to 64 bytes, by default empty string
   -- salt:     (optional) binary string up to 32 bytes, by default empty string
   -- digest_size_in_bytes: (optional) integer from 1 to 64, by default 64
   digest_size_in_bytes = digest_size_in_bytes or 64
   if digest_size_in_bytes < 1 or digest_size_in_bytes > 64 then
      error("BLAKE2bp digest length must be from 1 to 64 bytes", 2)
   end
   key = key or ""
   local key_length = #key
   if key_length > 64 then
      error("BLAKE2bp key length must not exceed 64 bytes", 2)
   end
   salt = salt or ""
   local instances, length, first_dword_of_parameter_block, result = {}, 0.0, 0x02040000 + key_length * 256 + digest_size_in_bytes
   for j = 1, 4 do
      local bytes_compressed, tail, H_lo, H_hi = 0.0, "", {unpack(sha2_H_lo)}, not HEX64 and {unpack(sha2_H_hi)}
      instances[j] = {bytes_compressed, tail, H_lo, H_hi}
      H_lo[1] = XORA5(H_lo[1], first_dword_of_parameter_block)
      H_lo[2] = XORA5(H_lo[2], j-1)
      H_lo[3] = XORA5(H_lo[3], 0x4000)
      if salt ~= "" then
         xor_blake2_salt(salt, "b", H_lo, H_hi)
      end
   end

   local function partial(message_part)
      if message_part then
         if instances then
            local from = 0
            while true do
               local to = math_min(from + 128 - length % 128, #message_part)
               if to > from then
                  local inst = instances[floor(length / 128) % 4 + 1]
                  local part = sub(message_part, from + 1, to)
                  length, from = length + to - from, to
                  local bytes_compressed, tail = inst[1], inst[2]
                  if #tail < 128 then
                     tail = tail..part
                  else
                     local H_lo, H_hi = inst[3], inst[4]
                     bytes_compressed = blake2b_feed_128(H_lo, H_hi, tail, 0, 128, bytes_compressed)
                     tail = part
                  end
                  inst[1], inst[2] = bytes_compressed, tail
               else
                  break
               end
            end
            return partial
         else
            error("Adding more chunks is not allowed after receiving the result", 2)
         end
      else
         if instances then
            local root_H_lo, root_H_hi = {unpack(sha2_H_lo)}, not HEX64 and {unpack(sha2_H_hi)}
            root_H_lo[1] = XORA5(root_H_lo[1], first_dword_of_parameter_block)
            root_H_lo[3] = XORA5(root_H_lo[3], 0x4001)
            if salt ~= "" then
               xor_blake2_salt(salt, "b", root_H_lo, root_H_hi)
            end
            for j = 1, 4 do
               local inst = instances[j]
               local bytes_compressed, tail, H_lo, H_hi = inst[1], inst[2], inst[3], inst[4]
               blake2b_feed_128(H_lo, H_hi, tail..string_rep("\0", 128 - #tail), 0, 128, bytes_compressed, #tail, j == 4)
               if j % 2 == 0 then
                  local index = 0
                  for k = j - 1, j do
                     local inst = instances[k]
                     local H_lo, H_hi = inst[3], inst[4]
                     for i = 1, 8 do
                        index = index + 1
                        common_W_blake2b[index] = H_lo[i]
                        if H_hi then
                           index = index + 1
                           common_W_blake2b[index] = H_hi[i]
                        end
                     end
                  end
                  blake2b_feed_128(root_H_lo, root_H_hi, nil, 0, 128, 128 * (j/2 - 1), j == 4 and 128, j == 4)
               end
            end
            instances = nil
            local max_reg = ceil(digest_size_in_bytes / 8)
            if HEX64 then
               for j = 1, max_reg do
                  root_H_lo[j] = HEX64(root_H_lo[j])
               end
            else
               for j = 1, max_reg do
                  root_H_lo[j] = HEX(root_H_hi[j])..HEX(root_H_lo[j])
               end
            end
            result = sub(gsub(table_concat(root_H_lo, "", 1, max_reg), "(..)(..)(..)(..)(..)(..)(..)(..)", "%8%7%6%5%4%3%2%1"), 1, digest_size_in_bytes * 2)
         end
         return result
      end
   end

   if key_length > 0 then
      key = key..string_rep("\0", 128 - key_length)
      for j = 1, 4 do
         partial(key)
      end
   end
   if message then
      -- Actually perform calculations and return the BLAKE2bp digest of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading
      -- User should feed every chunk of input data as single argument to this function and finally get BLAKE2bp digest by invoking this function without an argument
      return partial
   end

end

local function blake2x(inner_func, inner_func_letter, common_W_blake2, block_size, digest_size_in_bytes, message, key, salt)
   local XOF_digest_length_limit, XOF_digest_length, chunk_by_chunk_output = 2^(block_size / 2) - 1
   if digest_size_in_bytes == -1 then  -- infinite digest
      digest_size_in_bytes = math_huge
      XOF_digest_length = floor(XOF_digest_length_limit)
      chunk_by_chunk_output = true
   else
      if digest_size_in_bytes < 0 then
         digest_size_in_bytes = -1.0 * digest_size_in_bytes
         chunk_by_chunk_output = true
      end
      XOF_digest_length = floor(digest_size_in_bytes)
      if XOF_digest_length >= XOF_digest_length_limit then
         error("Requested digest is too long.  BLAKE2X"..inner_func_letter.." finite digest is limited by (2^"..floor(block_size / 2)..")-2 bytes.  Hint: you can generate infinite digest.", 2)
      end
   end
   salt = salt or ""
   if salt ~= "" then
      xor_blake2_salt(salt, inner_func_letter)  -- don't xor, only check the size of salt
   end
   local inner_partial = inner_func(nil, key, salt, nil, XOF_digest_length)
   local result

   local function partial(message_part)
      if message_part then
         if inner_partial then
            inner_partial(message_part)
            return partial
         else
            error("Adding more chunks is not allowed after receiving the result", 2)
         end
      else
         if inner_partial then
            local half_W, half_W_size = inner_partial()
            half_W_size, inner_partial = half_W_size or 8

            local function get_hash_block(block_no)
               -- block_no = 0...(2^32-1)
               local size = math_min(block_size, digest_size_in_bytes - block_no * block_size)
               if size <= 0 then
                  return ""
               end
               for j = 1, half_W_size do
                  common_W_blake2[j] = half_W[j]
               end
               for j = half_W_size + 1, 2 * half_W_size do
                  common_W_blake2[j] = 0
               end
               return inner_func(nil, nil, salt, size, XOF_digest_length, floor(block_no))
            end

            local hash = {}
            if chunk_by_chunk_output then
               local pos, period, cached_block_no, cached_block = 0, block_size * 2^32

               local function get_next_part_of_digest(arg1, arg2)
                  if arg1 == "seek" then
                     -- Usage #1:  get_next_part_of_digest("seek", new_pos)
                     pos = arg2 % period
                  else
                     -- Usage #2:  hex_string = get_next_part_of_digest(size)
                     local size, index = arg1 or 1, 0
                     while size > 0 do
                        local block_offset = pos % block_size
                        local block_no = (pos - block_offset) / block_size
                        local part_size = math_min(size, block_size - block_offset)
                        if cached_block_no ~= block_no then
                           cached_block_no = block_no
                           cached_block = get_hash_block(block_no)
                        end
                        index = index + 1
                        hash[index] = sub(cached_block, block_offset * 2 + 1, (block_offset + part_size) * 2)
                        size = size - part_size
                        pos = (pos + part_size) % period
                     end
                     return table_concat(hash, "", 1, index)
                  end
               end

               result = get_next_part_of_digest
            else
               for j = 1.0, ceil(digest_size_in_bytes / block_size) do
                  hash[j] = get_hash_block(j - 1.0)
               end
               result = table_concat(hash)
            end
         end
         return result
      end
   end

   if message then
      -- Actually perform calculations and return the BLAKE2X digest of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading
      -- User should feed every chunk of input data as single argument to this function and finally get BLAKE2X digest by invoking this function without an argument
      return partial
   end
end

local function blake2xs(digest_size_in_bytes, message, key, salt)
   -- digest_size_in_bytes:
   --    0..65534       = get finite digest as single Lua string
   --    (-1)           = get infinite digest in "chunk-by-chunk" output mode
   --    (-2)..(-65534) = get finite digest in "chunk-by-chunk" output mode
   -- message:  binary string to be hashed (or nil for "chunk-by-chunk" input mode)
   -- key:      (optional) binary string up to 32 bytes, by default empty string
   -- salt:     (optional) binary string up to 16 bytes, by default empty string
   return blake2x(blake2s, "s", common_W_blake2s, 32, digest_size_in_bytes, message, key, salt)
end

local function blake2xb(digest_size_in_bytes, message, key, salt)
   -- digest_size_in_bytes:
   --    0..4294967294       = get finite digest as single Lua string
   --    (-1)                = get infinite digest in "chunk-by-chunk" output mode
   --    (-2)..(-4294967294) = get finite digest in "chunk-by-chunk" output mode
   -- message:  binary string to be hashed (or nil for "chunk-by-chunk" input mode)
   -- key:      (optional) binary string up to 64 bytes, by default empty string
   -- salt:     (optional) binary string up to 32 bytes, by default empty string
   return blake2x(blake2b, "b", common_W_blake2b, 64, digest_size_in_bytes, message, key, salt)
end


local function blake3(message, key, digest_size_in_bytes, message_flags, K, return_array)
   -- message:  binary string to be hashed (or nil for "chunk-by-chunk" input mode)
   -- key:      (optional) binary string up to 32 bytes, by default empty string
   -- digest_size_in_bytes: (optional) by default 32
   --    0,1,2,3,4,...  = get finite digest as single Lua string
   --    (-1)           = get infinite digest in "chunk-by-chunk" output mode
   --    -2,-3,-4,...   = get finite digest in "chunk-by-chunk" output mode
   -- The last three parameters "message_flags", "K" and "return_array" are for internal use only, user must omit them (or pass nil)
   key = key or ""
   digest_size_in_bytes = digest_size_in_bytes or 32
   message_flags = message_flags or 0
   if key == "" then
      K = K or sha2_H_hi
   else
      local key_length = #key
      if key_length > 32 then
         error("BLAKE3 key length must not exceed 32 bytes", 2)
      end
      key = key..string_rep("\0", 32 - key_length)
      K = {}
      for j = 1, 8 do
         local a, b, c, d = byte(key, 4*j-3, 4*j)
         K[j] = ((d * 256 + c) * 256 + b) * 256 + a
      end
      message_flags = message_flags + 16  -- flag:KEYED_HASH
   end
   local tail, H, chunk_index, blocks_in_chunk, stack_size, stack = "", {}, 0, 0, 0, {}
   local final_H_in, final_block_length, chunk_by_chunk_output, result, wide_output = K
   local final_compression_flags = 3      -- flags:CHUNK_START,CHUNK_END

   local function feed_blocks(str, offs, size)
      -- size >= 0, size is multiple of 64
      while size > 0 do
         local part_size_in_blocks, block_flags, H_in = 1, 0, H
         if blocks_in_chunk == 0 then
            block_flags = 1               -- flag:CHUNK_START
            H_in, final_H_in = K, H
            final_compression_flags = 2   -- flag:CHUNK_END
         elseif blocks_in_chunk == 15 then
            block_flags = 2               -- flag:CHUNK_END
            final_compression_flags = 3   -- flags:CHUNK_START,CHUNK_END
            final_H_in = K
         else
            part_size_in_blocks = math_min(size / 64, 15 - blocks_in_chunk)
         end
         local part_size = part_size_in_blocks * 64
         blake3_feed_64(str, offs, part_size, message_flags + block_flags, chunk_index, H_in, H)
         offs, size = offs + part_size, size - part_size
         blocks_in_chunk = (blocks_in_chunk + part_size_in_blocks) % 16
         if blocks_in_chunk == 0 then
            -- completing the currect chunk
            chunk_index = chunk_index + 1.0
            local divider = 2.0
            while chunk_index % divider == 0 do
               divider = divider * 2.0
               stack_size = stack_size - 8
               for j = 1, 8 do
                  common_W_blake2s[j] = stack[stack_size + j]
               end
               for j = 1, 8 do
                  common_W_blake2s[j + 8] = H[j]
               end
               blake3_feed_64(nil, 0, 64, message_flags + 4, 0, K, H)  -- flag:PARENT
            end
            for j = 1, 8 do
               stack[stack_size + j] = H[j]
            end
            stack_size = stack_size + 8
         end
      end
   end

   local function get_hash_block(block_no)
      local size = math_min(64, digest_size_in_bytes - block_no * 64)
      if block_no < 0 or size <= 0 then
         return ""
      end
      if chunk_by_chunk_output then
         for j = 1, 16 do
            common_W_blake2s[j] = stack[j + 16]
         end
      end
      blake3_feed_64(nil, 0, 64, final_compression_flags, block_no, final_H_in, stack, wide_output, final_block_length)
      if return_array then
         return stack
      end
      local max_reg = ceil(size / 4)
      for j = 1, max_reg do
         stack[j] = HEX(stack[j])
      end
      return sub(gsub(table_concat(stack, "", 1, max_reg), "(..)(..)(..)(..)", "%4%3%2%1"), 1, size * 2)
   end

   local function partial(message_part)
      if message_part then
         if tail then
            local offs = 0
            if tail ~= "" and #tail + #message_part > 64 then
               offs = 64 - #tail
               feed_blocks(tail..sub(message_part, 1, offs), 0, 64)
               tail = ""
            end
            local size = #message_part - offs
            local size_tail = size > 0 and (size - 1) % 64 + 1 or 0
            feed_blocks(message_part, offs, size - size_tail)
            tail = tail..sub(message_part, #message_part + 1 - size_tail)
            return partial
         else
            error("Adding more chunks is not allowed after receiving the result", 2)
         end
      else
         if tail then
            final_block_length = #tail
            tail = tail..string_rep("\0", 64 - #tail)
            if common_W_blake2s[0] then
               for j = 1, 16 do
                  local a, b, c, d = byte(tail, 4*j-3, 4*j)
                  common_W_blake2s[j] = OR(SHL(d, 24), SHL(c, 16), SHL(b, 8), a)
               end
            else
               for j = 1, 16 do
                  local a, b, c, d = byte(tail, 4*j-3, 4*j)
                  common_W_blake2s[j] = ((d * 256 + c) * 256 + b) * 256 + a
               end
            end
            tail = nil
            for stack_size = stack_size - 8, 0, -8 do
               blake3_feed_64(nil, 0, 64, message_flags + final_compression_flags, chunk_index, final_H_in, H, nil, final_block_length)
               chunk_index, final_block_length, final_H_in, final_compression_flags = 0, 64, K, 4  -- flag:PARENT
               for j = 1, 8 do
                  common_W_blake2s[j] = stack[stack_size + j]
               end
               for j = 1, 8 do
                  common_W_blake2s[j + 8] = H[j]
               end
            end
            final_compression_flags = message_flags + final_compression_flags + 8  -- flag:ROOT
            if digest_size_in_bytes < 0 then
               if digest_size_in_bytes == -1 then  -- infinite digest
                  digest_size_in_bytes = math_huge
               else
                  digest_size_in_bytes = -1.0 * digest_size_in_bytes
               end
               chunk_by_chunk_output = true
               for j = 1, 16 do
                  stack[j + 16] = common_W_blake2s[j]
               end
            end
            digest_size_in_bytes = math_min(2^53, digest_size_in_bytes)
            wide_output = digest_size_in_bytes > 32
            if chunk_by_chunk_output then
               local pos, cached_block_no, cached_block = 0.0

               local function get_next_part_of_digest(arg1, arg2)
                  if arg1 == "seek" then
                     -- Usage #1:  get_next_part_of_digest("seek", new_pos)
                     pos = arg2 * 1.0
                  else
                     -- Usage #2:  hex_string = get_next_part_of_digest(size)
                     local size, index = arg1 or 1, 32
                     while size > 0 do
                        local block_offset = pos % 64
                        local block_no = (pos - block_offset) / 64
                        local part_size = math_min(size, 64 - block_offset)
                        if cached_block_no ~= block_no then
                           cached_block_no = block_no
                           cached_block = get_hash_block(block_no)
                        end
                        index = index + 1
                        stack[index] = sub(cached_block, block_offset * 2 + 1, (block_offset + part_size) * 2)
                        size = size - part_size
                        pos = pos + part_size
                     end
                     return table_concat(stack, "", 33, index)
                  end
               end

               result = get_next_part_of_digest
            elseif digest_size_in_bytes <= 64 then
               result = get_hash_block(0)
            else
               local last_block_no = ceil(digest_size_in_bytes / 64) - 1
               for block_no = 0.0, last_block_no do
                  stack[33 + block_no] = get_hash_block(block_no)
               end
               result = table_concat(stack, "", 33, 33 + last_block_no)
            end
         end
         return result
      end
   end

   if message then
      -- Actually perform calculations and return the BLAKE3 digest of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading
      -- User should feed every chunk of input data as single argument to this function and finally get BLAKE3 digest by invoking this function without an argument
      return partial
   end
end

local function blake3_derive_key(key_material, context_string, derived_key_size_in_bytes)
   -- key_material: (string) your source of entropy to derive a key from (for example, it can be a master password)
   --               set to nil for feeding the key material in "chunk-by-chunk" input mode
   -- context_string: (string) unique description of the derived key
   -- digest_size_in_bytes: (optional) by default 32
   --    0,1,2,3,4,...  = get finite derived key as single Lua string
   --    (-1)           = get infinite derived key in "chunk-by-chunk" output mode
   --    -2,-3,-4,...   = get finite derived key in "chunk-by-chunk" output mode
   if type(context_string) ~= "string" then
      error("'context_string' parameter must be a Lua string", 2)
   end
   local K = blake3(context_string, nil, nil, 32, nil, true)           -- flag:DERIVE_KEY_CONTEXT
   return blake3(key_material, nil, derived_key_size_in_bytes, 64, K)  -- flag:DERIVE_KEY_MATERIAL
end



local sha = {
   md5        = md5,                                                                                                                   -- MD5
   sha1       = sha1,                                                                                                                  -- SHA-1
   -- SHA-2 hash functions:
   sha224     = function (message)                       return sha256ext(224, message)                                           end, -- SHA-224
   sha256     = function (message)                       return sha256ext(256, message)                                           end, -- SHA-256
   sha512_224 = function (message)                       return sha512ext(224, message)                                           end, -- SHA-512/224
   sha512_256 = function (message)                       return sha512ext(256, message)                                           end, -- SHA-512/256
   sha384     = function (message)                       return sha512ext(384, message)                                           end, -- SHA-384
   sha512     = function (message)                       return sha512ext(512, message)                                           end, -- SHA-512
   -- SHA-3 hash functions:
   sha3_224   = function (message)                       return keccak((1600 - 2 * 224) / 8, 224 / 8, false, message)             end, -- SHA3-224
   sha3_256   = function (message)                       return keccak((1600 - 2 * 256) / 8, 256 / 8, false, message)             end, -- SHA3-256
   sha3_384   = function (message)                       return keccak((1600 - 2 * 384) / 8, 384 / 8, false, message)             end, -- SHA3-384
   sha3_512   = function (message)                       return keccak((1600 - 2 * 512) / 8, 512 / 8, false, message)             end, -- SHA3-512
   shake128   = function (digest_size_in_bytes, message) return keccak((1600 - 2 * 128) / 8, digest_size_in_bytes, true, message) end, -- SHAKE128
   shake256   = function (digest_size_in_bytes, message) return keccak((1600 - 2 * 256) / 8, digest_size_in_bytes, true, message) end, -- SHAKE256
   -- HMAC:
   hmac       = hmac,  -- HMAC(hash_func, key, message) is applicable to any hash function from this module except SHAKE* and BLAKE*
   -- misc utilities:
   hex_to_bin    = hex_to_bin,     -- converts hexadecimal representation to binary string
   bin_to_hex    = bin_to_hex,     -- converts binary string to hexadecimal representation
   base64_to_bin = base64_to_bin,  -- converts base64 representation to binary string
   bin_to_base64 = bin_to_base64,  -- converts binary string to base64 representation
   -- old style names for backward compatibility:
   hex2bin       = hex_to_bin,
   bin2hex       = bin_to_hex,
   base642bin    = base64_to_bin,
   bin2base64    = bin_to_base64,
   -- BLAKE2 hash functions:
   blake2b  = blake2b,   -- BLAKE2b (message, key, salt, digest_size_in_bytes)
   blake2s  = blake2s,   -- BLAKE2s (message, key, salt, digest_size_in_bytes)
   blake2bp = blake2bp,  -- BLAKE2bp(message, key, salt, digest_size_in_bytes)
   blake2sp = blake2sp,  -- BLAKE2sp(message, key, salt, digest_size_in_bytes)
   blake2xb = blake2xb,  -- BLAKE2Xb(digest_size_in_bytes, message, key, salt)
   blake2xs = blake2xs,  -- BLAKE2Xs(digest_size_in_bytes, message, key, salt)
   -- BLAKE2 aliases:
   blake2      = blake2b,
   blake2b_160 = function (message, key, salt) return blake2b(message, key, salt, 20) end, -- BLAKE2b-160
   blake2b_256 = function (message, key, salt) return blake2b(message, key, salt, 32) end, -- BLAKE2b-256
   blake2b_384 = function (message, key, salt) return blake2b(message, key, salt, 48) end, -- BLAKE2b-384
   blake2b_512 = blake2b,                                                      -- 64       -- BLAKE2b-512
   blake2s_128 = function (message, key, salt) return blake2s(message, key, salt, 16) end, -- BLAKE2s-128
   blake2s_160 = function (message, key, salt) return blake2s(message, key, salt, 20) end, -- BLAKE2s-160
   blake2s_224 = function (message, key, salt) return blake2s(message, key, salt, 28) end, -- BLAKE2s-224
   blake2s_256 = blake2s,                                                      -- 32       -- BLAKE2s-256
   -- BLAKE3 hash function
   blake3            = blake3,             -- BLAKE3    (message, key, digest_size_in_bytes)
   blake3_derive_key = blake3_derive_key,  -- BLAKE3_KDF(key_material, context_string, derived_key_size_in_bytes)
}


block_size_for_HMAC = {
   [sha.md5]        =  64,
   [sha.sha1]       =  64,
   [sha.sha224]     =  64,
   [sha.sha256]     =  64,
   [sha.sha512_224] = 128,
   [sha.sha512_256] = 128,
   [sha.sha384]     = 128,
   [sha.sha512]     = 128,
   [sha.sha3_224]   = 144,  -- (1600 - 2 * 224) / 8
   [sha.sha3_256]   = 136,  -- (1600 - 2 * 256) / 8
   [sha.sha3_384]   = 104,  -- (1600 - 2 * 384) / 8
   [sha.sha3_512]   =  72,  -- (1600 - 2 * 512) / 8
}

local function test_sha256()

   local sha256 = sha.sha256

   -- some test strings
   assert(sha256("abc") == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
   assert(sha256("123456") == "8d969eef6ecad3c29a3a629280e686cf0c3f5d5a86aff3ca12020c923adc6c92")
   assert(sha256("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") == "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")
   assert(sha256("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu") == "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1")
   assert(sha256("The quick brown fox jumps over the lazy dog") == "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592")
   assert(sha256("The quick brown fox jumps over the lazy cog") == "e4c4d8f3bf76b692de791a173e05321150f7a345b46484fe427f6acc7ecc81be")

   -- chunk-by-chunk loading:   sha256("string") == sha256()("st")("ri")("ng")()
   local append_next_chunk = sha256() -- create a private closure for calculating digest of single string
   append_next_chunk("The quick brown fox")
   append_next_chunk(" jumps ")
   append_next_chunk("")              -- chunk may be an empty string
   append_next_chunk("over the lazy dog")
   assert(append_next_chunk() == "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592")  -- invocation without an argument means "give me the result"
   assert(append_next_chunk() == "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592")  -- you can ask the same result multiple times if needed
   assert(not pcall(append_next_chunk, "more text"))  -- no more chunks are allowed after receiving the result, append_next_chunk("more text") will fail

   -- one-liner is possible due to "append_next_chunk(chunk)" returns the function "append_next_chunk"
   assert(sha256()("The quick brown fox")(" jumps ")("")("over the lazy dog")() == "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592")

   -- empty string
   assert(sha256("") == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
   assert(sha256()() == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")

   -- two parallel computations don't interfere with each other
   local chunk_for_digits = sha256()
   chunk_for_digits("123")
   local chunk_for_fox = sha256()
   chunk_for_fox("The quick brown fox jumps ")
   chunk_for_digits("45")
   chunk_for_fox("over the lazy dog")
   chunk_for_digits("6")
   assert(chunk_for_digits() == "8d969eef6ecad3c29a3a629280e686cf0c3f5d5a86aff3ca12020c923adc6c92")
   assert(chunk_for_fox() == "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592")

   -- "00...0\n"
   for i, dgst in pairs{  -- from 50 to 70 zeroes
      [50] = "9660acb8046abf46cf27280e61abd174ebac98ad6855e093772b78df85523129",
      [51] = "31e1c552b357ace9bcb924691799a3c0d3aa10d8b428d9de28a278e3c79ecb7b",
      [52] = "0be5c4bcb6f47e30c13515594dbef4faa3a6485af67c177179fee8b33cd4f2a0",
      [53] = "d368c7f6038c1743bdbfe6a9c3a72d4e6916aa219ed8d559766c9e8f9845f3b8",
      [54] = "7080a4aa6ff030ae152fe610a62ee29464f92afeb176474551a69d35aab154a0",
      [55] = "149c1cda81fa9359c0c2a5e405ca972986f1d53e05f6282871dd1581046b3f44",
      [56] = "eb2d4d41948ce546c8adff07ee97342070c5b89789f616a33efe52c7d3ec73d4",
      [57] = "c831db596ccbbf248023461b1c05d3ae084bcc79bcb2626c5ec179fb34371f2a",
      [58] = "1345b8a930737b1069bbf9b891ce095850f6cdba6e25874ea526a2ccb611fe46",
      [59] = "380ad21e466885fae080ceeada75ac04944687e626e161c0b24e91af3eec2def",
      [60] = "b9ab06fa30ef8531c5eee11651aa86f8279a245e0a3c29bf6228c59475cc610a",
      [61] = "bcc187de6605d9e11a0cc6edf02b67fb651fe1779ec59438788093d8e376c07c",
      [62] = "ae0b3681157b83b34de8591d2453915e40c3105ae79434e241d82d4035218e01",
      [63] = "68a27b4735f6806fb5983c1805a23797aa93ea06e0ebcb6daada2ea1ab5a05af",
      [64] = "827d096d92f3deeaa0e8070d79f45beb176768e57a958a1cd325f5f4b754b048",
      [65] = "6c7bd8ec0fe9b4e05a2d27dd5e41a8687a9716a2e8926bdfa141266b12942ec1",
      [66] = "2f4b4c41017a2ddd1cc8cd75478a82e9452e445d4242f09782535376d6f4ba50",
      [67] = "b777b86e005807a446ead00986fcbf3bdd6c022524deabf017eeb3f0c30b6eed",
      [68] = "777da331f60c793f582e4ca33223778218ddfd241981f15be5886171fb8301b5",
      [69] = "06ed0c4cbf7d2b38de5f01eab2d2cd552d9cb87f97b714b96bb7a9d1b6117c6d",
      [70] = "e82223344d5f3c024514cfbe6d478b5df98bb878f34d7a07e7b064fa7fa91946"
   } do
      assert(sha256(("0"):rep(i).."\n") == dgst)
   end

   -- "aa...a"
   assert(sha256(("a"):rep(55)) == "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318")
   assert(sha256(("a"):rep(56)) == "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a")

   -- negative byte values
   assert(sha256(("\255"):rep(1e3)) == "b4f73dff046400b76728ab32619e3d89e00132653725f660c62ab9fca975b372")

   -- "aa...a\n" in "chunk-by-chunk" mode
   local next_chunk = sha256()
   for i = 1, 65 do
      next_chunk("a")
   end
   next_chunk("\n")
   assert(next_chunk() == "574883a9977284a46845620eaa55c3fa8209eaa3ebffe44774b6eb2dba2cb325")
   -- "aa...a\n" in "whole-string" mode
   assert(sha256(("a"):rep(65).."\n") == "574883a9977284a46845620eaa55c3fa8209eaa3ebffe44774b6eb2dba2cb325")

   local function split_and_calculate_sha256(s, len) -- split string s in chunks of length len
      local next_chunk = sha256()
      for idx = 1, #s, len do
         next_chunk(s:sub(idx, idx + len - 1))
      end
      return next_chunk()
   end
   -- "00...0\n00...0\n...00...0\n" (80 lines of 80 zeroes each) in chunk-by-chunk mode with different chunk lengths
   local s = (("0"):rep(80).."\n"):rep(80)
   assert(split_and_calculate_sha256(s, 1)   == "736c7a8b17e2cfd44a3267a844db1a8a3e8988d739e3e95b8dd32678fb599139")
   assert(split_and_calculate_sha256(s, 2)   == "736c7a8b17e2cfd44a3267a844db1a8a3e8988d739e3e95b8dd32678fb599139")
   assert(split_and_calculate_sha256(s, 7)   == "736c7a8b17e2cfd44a3267a844db1a8a3e8988d739e3e95b8dd32678fb599139")
   assert(split_and_calculate_sha256(s, 70)  == "736c7a8b17e2cfd44a3267a844db1a8a3e8988d739e3e95b8dd32678fb599139")
   assert(split_and_calculate_sha256(s, 1e6) == "736c7a8b17e2cfd44a3267a844db1a8a3e8988d739e3e95b8dd32678fb599139")

end


local function test_sha512()

   local sha512 = sha.sha512

   assert(sha512("abc") == "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")
   assert(sha512("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu") == "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909")

   -- "aa...a"
   for i, dgst in ipairs{  -- from 1 to 140 letters "a"
      [001] = "1f40fc92da241694750979ee6cf582f2d5d7d28e18335de05abc54d0560e0f5302860c652bf08d560252aa5e74210546f369fbbbce8c12cfc7957b2652fe9a75",
      [002] = "f6c5600ed1dbdcfdf829081f5417dccbbd2b9288e0b427e65c8cf67e274b69009cd142475e15304f599f429f260a661b5df4de26746459a3cef7f32006e5d1c1",
      [003] = "d6f644b19812e97b5d871658d6d3400ecd4787faeb9b8990c1e7608288664be77257104a58d033bcf1a0e0945ff06468ebe53e2dff36e248424c7273117dac09",
      [004] = "1b86355f13a7f0b90c8b6053c0254399994dfbb3843e08d603e292ca13b8f672ed5e58791c10f3e36daec9699cc2fbdc88b4fe116efa7fce016938b787043818",
      [005] = "f368a29b71bd201a7ef78b5df88b1361fbe83f959756d33793837a5d7b2eaf660f2f6c7e2fbace01965683c4cfafded3ff28aab34e329aa79bc81e7703f68b86",
      [006] = "7a9b2a35095dcdfedfdf0ef810310b409e38c92c20cbd51088ea5e4bc4873bdacfeb29f14b7f2ed033d87fad00036da83d5c597a7e7429bc70cec378db4de6a6",
      [007] = "d1ff70451d1f0b94f551461c5ca239e498f571add4542c381e3eef84eac24aea6d12f8333ef4a05847e205ef4bb094921314364e7648176f567863d982042a85",
      [008] = "f74f2603939a53656948480ce71f1ce466685b6654fd22c61c1f2ce4e2c96d1cd02d162b560c4beaf1ae45f3471dc5cbc1ce040701c0b5c38457988aa00fe97f",
      [009] = "507294e03fdbc784dc3f575706c3ce53b3c4c37065e89ddd6b6de8bd2be655e15412e27695d32d2d6a3a0eaabe36ebddde78af0122a65ec41128c98c6fd30554",
      [010] = "4714870aff6c97ca09d135834fdb58a6389a50c11fef8ec4afef466fb60a23ac6b7a9c92658f14df4993d6b40a4e4d8424196afc347e97640d68de61e1cf14b0",
      [011] = "2d5be0f423fee59bf2149f996e72d9f5f8df90540a7d23b68c0d0d9a9a32d2c144891ca8fe4a3c713cb6eb2991578541dad291ba623dbd7107c6a891ba00bcc8",
      [012] = "a88ac22ca41e71e252c1f0d925de1ec174346e097c695e948d23016ab54cf21da6f0b0490ffa752bcc4893afc0c2caa64307705d1996f2959a3e03dc420c68cf",
      [013] = "b0b8828df9473f2763f9a48b0a9683451e98155436c2eff64c628fedbba0cca2360312271f3971f2969b1f828b1bb8251d3a43e12361824aca14f9a9affe2171",
      [014] = "831ce89c92608efda86cdf89d36e855bc73c5d17b2162c0013c14a2676ef4794dc53de6a54c1e3fb782acef5dd1192d36d0ab7fa88262cf0f6a16950e44a828c",
      [015] = "0b6f7fb0679a1ef009d5c8c70551d3b7013a5881b41ec2d597c3cf22e6aa13a1cf9a925b7a012feb67956c83b91cc32bef1de4cdbc6b2ff0cffbba319b54d15e",
      [016] = "987d0fc93db6a73fdb16493690fb42455c7c6fbafe9a276965424b12afad3512fb808d902faa8a019d639dc5ad07c235805e08f396147cf435913cfed501f65a",
      [017] = "06ef0364617146f6200c2cbc4280202226d701c2961940f57e7b60677587c66087f23bbcffa0de8692221f9434ac9a21e6df6428377cd145e1a456e2359d2cf6",
      [018] = "10dbd292472d3ff7279f3dac7fdb83c296bd61cbe80b0e26fbc14f871fd9771180d83879e812ec9841ba15a110e84a589c0eedfc14427c23ba56fa4fb7773de0",
      [019] = "1d383178e64d7071e749b2d560a22abc97e6514c31e800b5cc12c6f72ad43a9a0c4ce7db246219f3dea09afae6044a484de203148cb55f1057ee37b9420073bb",
      [020] = "d87a10a0bee363dcdf764831e807df5ee5500483c09056b38f854606f9e665566264b15af9fee8f9b84f3a7b6ddb67b92996ef790d10e899ba0758d5ab650caf",
      [021] = "1f60925cd5271a8ec9eb49ea4bf187f6a7dbc22eeb0e2dbc89d8381d0e73dea5bff5375a6db7e49fc427cb4fdf9f7ece577037adf91decfc38f303b1cb79ad44",
      [022] = "0ff3b2ffbda4cf938263e9449735618103a4d6a0cdeeda57367f6377d23849c3dce6851377f8f1b3d2ce3ff1dd6de0d64920d7790994782b4a8e2697e31f1900",
      [023] = "c6020ac00b701699227ccc9355156da0ad1d521ada5949cc89dd00661725be08fea4a2519ceb1e50acdd16e7127783f7ed5bfabe5238ce0da7ad2b4174c5509a",
      [024] = "e37ff6da226042c6fdd066c20f00e0d09c4f4dea104d8ea1fc513496ef24a0e17cd4bfb2e95781329a45d3885ca0e20f88e453dc9a4c4dc2acd0be756e3356b8",
      [025] = "4d272d73d4000f885ad1be048b7c7f92c2a8e5a01f30a96ed82849223606ad639f73155c85a128fbd2c26d3de30fb207e57b9f7ff21bfc79e0d7f0e2fb5189dc",
      [026] = "90cce547b76967676972c60e83944ffdc143078b6b40c722a0f2ac90d78eed0057843213076a9a7df528d0c0ebf3c00a91ae1c37f8850173fa2c03c41b6168ea",
      [027] = "4cea8c7ef657f9177c286081f8f016adae91a131a496e939ac86060e691afba57accc08ddbc423eb9d0817725faad9554c60f314929f30e881871e8782228918",
      [028] = "24077df741cb7ba88537d62c55fbff3ea81b603c31e6fd0d2e5d28e1a505f6192d5b2c1f98011152fef2c75901f66d489c045a4a3f98705c2b244c004f1579d4",
      [029] = "2af97e464526c024ef466db4616559919b769b350b7f6830ecfa5ffdeacd6eb570daf0ed25c0c56b194119f15247f63f5b94b54e01283b4b7a832586acac9e09",
      [030] = "abd9c33f8c791b27dd614e80ad77f1ff33c2621663b4dcbe5a88417a8b95b8d6788a9320678b589aa5b405897b2113523df1defa304953ea2ae1a229f2736450",
      [031] = "ad9e7ae1f68786c33ca713d4632b29ebcc9c9c040fc176ead8acb395a14c08324e824f7531f6a50ba0d4a17de958a08e54c9597dcc30781e22c0d953d06f9f4d",
      [032] = "020089a47cb0761c222c323aec2bdecdaa7a0d0ec094cda8c5755ba26844453c25b37e4bc98aab8adc55c9da75bcd83af62905d62e9044a5d64cd93d93b54b34",
      [033] = "d578a2d3fab982fbc7f1fa20630713c5a2a2cd9654a53822978d3efd2becc2a02e1fa1391dd11e139d1489aba688367ea9286e2a9ba8ef67009c80df81998614",
      [034] = "c1de14e1a09b03c688bd568ff4b4fa086baed2181d0d99a219fb937484ba67f093efe36966b0ea5209dadb6ef4f67c2d1f753d49c083a6241d2ab4557509404e",
      [035] = "cbb50e7e8a14cb9df08642609b6d737302d78cdcff74e1f53e895ae4a7cb093a571364dbbc2797962f54366ef65ead1c41a44ffe2ab0d56b7ae01e99a7a4e6fb",
      [036] = "85a564722dbefd268ed2e2e70fb377306c207a9c7edb634adcd79b8829aaad700c3a26cce44eba99aff46c4349f5e5056a87fcd2b63dd08b8b7b1f2f3ea06d6b",
      [037] = "ae77859a42c40e3973aa42bc8fbe8713444f65173580507d7c4bcc7c85d7f8c93204f433d506e912504ea37c766af17e649bdf6c8356f6e8e65bf4e9321987cb",
      [038] = "5b7c791e8018b14752ca7b91386d3ddbd3f9307a69ca71d977e274171aa5cae0b1a03960e842ca05fc0b95205a243fc8b28c36e4dd60ff000a47fb63547e6a0c",
      [039] = "f140bd9a11c309eb9da6ae1c8360cf2bc952a41a9ff228c066c0811df508313f59f1b6e6ffc6d14ef967f477c69463974aefd78d1c1dec9d8d35ff0c81dc29e8",
      [040] = "e411795f8b2a38c99a7b86c888f84c9b26d0f47f2c086d71a2c9282caf6a898820e2c1f3dc1fa45b20178da40f6cb7e4479d3d7155845ed7a4b8698b398f3d0c",
      [041] = "9178f65d74628c56ce3ace5b9ae7ecb84fc8a840ae33367a9c5534e6556301dc4fea4927d82289483496c39b929afb4a4ea92ded82c02057a7b8029828d8fb8d",
      [042] = "e11e1d056266f561bf3a9dede38228700e59971b3be992fea66a687887441976d8b29193707211dfb94dd1f7918473c3e99ff48a7c91068a1aaf7054febb9e2d",
      [043] = "acbaf243155ab6ca5f44c13061757fa060acbc5cf43d996b4f47209c22bf70c29af8dbc5c0a68ca45e42142db1540d2db70f6f27a917a3019dc92dadd0f639d6",
      [044] = "647b6deadb5aeb56e4087414fe2a76d6f57083dd6303a19e152445d108dc2bcd17926981d500b19b913b36a3b343b2e6781c805c1897664a218a2cfecc6a5238",
      [045] = "3ca97cdefcc384485ec2b6bebffe63d98f5675132a8b43d1f38bad4ff1982264fc4876ec637e918f855d855945b9b84eb82386bc6fc1e92695ec623001f8ddd1",
      [046] = "7b549433b4ef39abb90dcd3eb90c63562b7f3daa056670b2f712ebb7e9e78adfe7423e4b39810c1109fb640e84d32047468b155fe342d13e7f4d7ee019fa5922",
      [047] = "ec1d753e2280b8136b686ec81b03b3f8a7f98152868e3a68f0a2c456082c2faaa93c39ad573a6d21f4a3350df602249dc89ad28620d27ecc1d9e1f258badcd04",
      [048] = "bd582a787a21036df7049d501879977625601527d7ddd6f707463cb8b3839fbedbe233b8e69f1696d0e82b168d3491a3dbb6005b6224c198601dafbd50e14365",
      [049] = "4b4ff3bc763a976c16afdd8082efc7a5c98d60342f0ed5a654f567dacbc6414833e60ed1d6770bd42638fdae605c69be0219532125a186609f0825376ab59e45",
      [050] = "bdba173e58132092b0aa67ea5080f247e5b3710630a789c519b311f3848588f0bac8db3091ff8fd16875601636bef625e43b3d82cb51eb6693cdd1b2a5c872b8",
      [051] = "78a0eb5d7c0b05284056e1f19cbb42a99470bc81de4f9bc48708d28c5a877626e69167c58d4e840a7aa699bc6dddd972564d84ea502b41d83878e98e68f83c81",
      [052] = "a45021322d3f30747b3ceb7c1b1975ac4698984be76915f82cdeefe769f115d9dc5c70549e897b0ab8d5d61fc9e73ad1f7f49db39bb4e1298ac833d290eb1d04",
      [053] = "0b08accaae7044e54074fdcb7404a10c0703144d4499a644d9cfc60f973dc27dcdc65ac31750f7407ba96d025fb699e64ddcd1acd0dabafeeafccb5733225d3b",
      [054] = "07a2200290a2b7423a94f71892554b17196e2301e2e446ce09f65abcb45523268274128038925489671af9b899747b80e35a0a1b8613ecfb44e6be3152a2fd93",
      [055] = "b0220c772cbf6c1822e2cb38a437d0e1d58772417a4bbb21c961364f8b6143e05aa6316dca8d1d7b19e16448419076395f6086cb55101fbd6d5497b148e1745f",
      [056] = "962b64aae357d2a4fee3ded8b539bdc9d325081822b0bfc55583133aab44f18bafe11d72a7ae16c79ce2ba620ae2242d5144809161945f1367f41b3972e26e04",
      [057] = "d3115798e872fc1ca6b276368e8ea0926daec6ab1f8f08297e4348ff5f5fe4c6e5205413271babafd4929b070754bc5800e5db44790666ec4e2f6ac52a17e163",
      [058] = "2282084c042e92d7ba1a9e1ee5527762e91c4ffee7a8676c4a4a0facefad352bed2d3c322368cfe813186084c5386e9f22f803dfe0a1b424cab3e0a95a6dc3f9",
      [059] = "fd4eaf2071e8d9cf36688c3be714f5e363a5b4932f509914c613d1b8987d188e82cdd12b6ab07ea2f676fad1789275ef37253260a817a61079bc0ea567ee094a",
      [060] = "5ac08e89d884de3f086c60e8f36e754cf0ae9be2f018a87b7f71b15c81356410077eaa075010eb48959783ba490dc7c9fec53573848d8929bd5fc0574552f58f",
      [061] = "0202004b03bf7be513c96ef3fa6e48fce6e02f858d3bd95edba5adbdce60b2d7a4aa8700de15fc421b5e6847d8fb8be1bd24acd16314cfd94f0fa69ff6d637b4",
      [062] = "9814d48ae1bfd731b32f0a829f20507ec9bd6b77609053718f7e2053b53c7a264bbab6a96d3d54a7f9a736570d11b1f99afb1735149f43cfee9b6f87886d3ff6",
      [063] = "c1b0f5c6d3b03dfe4a2602e67242f54e344090b66e01100a469b129f583f016c7e27dddeaa438393dcc7ec54b0b57c9ba7af007f9b56db5f6fb677d972a31362",
      [064] = "01d35c10c6c38c2dcf48f7eebb3235fb5ad74a65ec4cd016e2354c637a8fb49b695ef3c1d6f7ae4cd74d78cc9c9bcac9d4f23a73019998a7f73038a5c9b2dbde",
      [065] = "b83086cd8494e55708ad7ecd82dfb4bca1bda61ecbb7caf0c68967902e709345e5d8305eb7ac0d588afc6cbb75161aa9c8c7e0ea986bd833dafe5e1ccd37345a",
      [066] = "f2f1cb2b1da21f7df43034baf8ec6bc992a46a022a40f81339240fdae572dbdf34fcf26e97cabc0e001c0aa65607b45585d107c48d676d6e2f389fd801d1fed7",
      [067] = "1b049c5022acb0a6f886cb607629db83dee7ee8f623f8f0fcf352b8f5052036cc7e992e9f79bc424173abb07df8ccfb058f13cfe2a14925a1bb67f4447dd8929",
      [068] = "6c450032dd6b928bdb327b9892d15808163d314aeff37089380ca01ee4b1c8db739f71de29446c385fc8e0f12482ccb04ca1572e243affc7d77ed7bbc083be0d",
      [069] = "73fa82cfc129fb937094b53346e04ff29e44c67250f6952b63ef561bc7cc1169fd94368a252ae408f496c17684145d65cd46ec9c5a03eb59ecc35f6a1d2fc159",
      [070] = "d7ef283e6194befc2498bbced7f58bdf60cfcf10011fc5817b69cb13d63725017aa1e632ea3c609f6a5eb8a057ddb82953538f3e2a738262a11ddcd47f13752d",
      [071] = "216d4ffba1e94e8f281b06feb558346eeb0ae567c0a1d0c56ba2df704f45b2a6e6d91f97c5c00ebbcdfeb14b438bd9e56f2eb36ca64d22392520f3496f28fef5",
      [072] = "7e076f0892677d21072e99258203151146d4bc78ad6ed68edc939ba080c473ab66b10d38834e33abde71830dbd8529d895c7ea5f5773f1457d7c71bc3824b7c8",
      [073] = "1a3d403b46c595edfb71d10b4cb9e1b9ce4e44e28db6ba2a0334195816b85e6eba147bc6160864a0fe28166f99148476893a031a38a814e7136497296865f3c9",
      [074] = "4c4c8dcd6ba88f47a51df4dabdf227c335d70d5f4941b76e698536693e53c50241ef0264ea6f6dc5527485ddbe7a76900405158e32fef5ed184919943148da67",
      [075] = "8ea2d14c839946461666ab0a5966a10886e29d0a890104b123bb94d0af9011d8a961681fb95df98d00d5d351985f61f2e2eba2d91fd8032566b856d8408a09b0",
      [076] = "c642ba36e76cc1660c342d163fb32e4be8482072e641dd6b3662c447ecbc24f1b5e16ad4b83eed093c6f5999f1b2a0086fc23526cef9241a5a052c720bb5afde",
      [077] = "b9451e8c39c4276c2192939d49cbcb2b85a048e4f38bb5d3282e24c417de893ac2ff0acdef20036ed4deddbb526f992cd56f992aaba93d4edd3a628a4e53c811",
      [078] = "9a8c06cf6123391e9ee4d2441b7e534fc9551c242fb2b96fad45a7210edc010c36704b9ca1a07e935e6ff1413768e2f27726b213b16961633341ea82d75c5df3",
      [079] = "54b998867e8ac0d3eebcbf2252c107ad6dc5b557db5b7cb65a147475db99831011878784a62678a6fada687705ef68d048047f05b51db9c09168c4a7ad877036",
      [080] = "cb8d0d18db405d9d964ab61d1a5c00024df3805a329bf1500bec74d3ec1f1d0574da0b86153c9d8e317603bdb09e46d54d44551992a2464f0335a8398a2f2aee",
      [081] = "2fe6df89dcac80c7a03c2bc39633c12ae2898019117aacf77e490fa54cb8deb34a0d29ce778ee4f674831921853a15b541773486d5ac785163744e6d24ba388d",
      [082] = "c3e410354f6f890d0f3027805da471340f91db2a858501059124d3175eb7d637ca3637f7f95bafde0d74d026be7bf086e48931e299d68edc43e0a7ac4eac75c4",
      [083] = "107068fb436d658c0a96157316af41d323e582ea9c81146933ead563bf2c2a05b2c77ceeef57c01cd09ec28f6507238e930b1b7241d731f83194440f9256e5a6",
      [084] = "62b5337f5be290d028dc41dde08682ed7b0a7a842eae36dc6f7220e220012aeca98b2dac28325d1f78beef84352689c07c3a45f549e98ba908b010abceca9978",
      [085] = "6b6f3ac1316d9e8d1505ad163b70077df1df92568139721b32c23e5d84dc2fd742a4bad56bf0efacb3f3e63bbfb08a829b16df8cc1799eb199cd5d56be2b9d52",
      [086] = "bf8ed43d3aeebeb9b00d91013fbbb463b2f4b13e7ffc42741aeb9f0190a91b0401bb4fac68cc009d314287876c54d2f18891e6eee86fbe7125171559be6a03d7",
      [087] = "056ffe9a8b3a346abb92cf36efb74417748a044c4ca07f94e7bb076eeafa67073a85fcc1b17e7953138f304bbea7d0592e910e55b489e22c9015dc4e04ba76dc",
      [088] = "a945652aabf28d5ed6bb284a35fd4296a9a0ddebc81bf59991759ecaa7fb95a59628cf1ae75c88177fa3993e0cd0f138a807cdc01d17ca3922817ad1dc1c39e7",
      [089] = "bb4ec00ac4a82ed71af3936559c5940582218da063554c6f3efbb6d67cc808a2d6dbf088d0f371a4a1259efb1f1edeefa8093cab25551519d7ac6142711e50fe",
      [090] = "3a60fa8bede0f822c5dea75eff151ed5841d11b301c474a13571aff2dd0e216b4bc072b9ce409a70c6e6ff35bcae2f0950880d943f95775dd8f54d94b12d47c3",
      [091] = "bed8ac47aef0271fe40227247ddcdfd6b4885effeba3042f34b6fd525ab56cbdf72050cb71b1d42ae0ee1c548b36668b9297279d661380dffa39e66aa2959f99",
      [092] = "dfecce5852f67e858304fc5dc0c15cb29e28c69af4e2c117d333ea46d2ef2b0379a983507bc16e827b86c2433404159b759de91eb9ae975f338bacf38ad20371",
      [093] = "51585d172675d427009ea1658ac2a4d67a600e65034cb7f8eb34a39add704b67ae0a2798b7d7e7a16ee0f6902a165a0646cd9fe1cc777a07c6bfa14028c8eec8",
      [094] = "9e4246d4d3725a67a909dd1a4f06c627627942c0bb31eb4c614cab842e6bfb9faa7e8938575a2402832ac353a6fb47f4918b31d754eb9764e714f6925462b54e",
      [095] = "89e0446c3ff5a04b6d707ef43a77e2b349791f402930dbdb74bbab73d5215e294146ba7bd2fa269aee38564ef11a9ccaf5278f9e82687126dcf20d481d470617",
      [096] = "39ba3c74b23cb7deffb5d59624e320c08692637057daaaeea4d847e1d3b6a2ce6895ff3c609d57da490484b030ed231d5bdfafcfe264bd3d91cddb39c2d036ab",
      [097] = "db3a1fb5909f50e02e1626616247de6867e9e332d0eeef4650367cf0058f4764eb4a3869d3931b5ef6fc7a044a868b5fa894462df15c3954e88cd70c9a1de1b2",
      [098] = "86497b815f64702e2ac6aca1f1d16f7159b4f0b34f6e92a41e632982a7291465957e0ef171042b9630bb66c6e35051613f99bdc95c371eeb46bff8c897eba6e9",
      [099] = "21883a9b2ffa353c93fea49ea8b92be22797e6e8b360ebac8ed894b702766458a825adf67d9561d6758f5f9cc3aec7a4b2e4464a08e6959029dbc0b2f3fc6105",
      [100] = "70ff99fd241905992cc3fff2f6e3f562c8719d689bfe0e53cbc75e53286d82d8767aed0959b8c63aadf55b5730babee75ea082e88414700d7507b988c44c47bc",
      [101] = "2327e3b2946432dd2f4bce390ca652ec5e90f44fced0e921f612cf6d594cfc5e21b56e30a30dc0157e2c37a59cd37951f20cb9e2bc2d815a2676c01c2f827d51",
      [102] = "ec90d76ee1a1643126f53609a2721ad4a130c57d4dd0416a5d1b0bc43419ed6b3b0e82e0ff5eb76e94accfacb8bf72d7c92b622a0842d9a5b8b6e40fa2fc5231",
      [103] = "48e257ba5ef0c4b0b9769d26d5990d87f058430e368802c1f9a47195a6fa23ede9bbadc4c46ef2a8480cbfa0ced25dad522ca1752a66d5b43a72486f82c7b934",
      [104] = "e4f39bcd76fe94bfa84b31b0b9f3d2fe065b1e01ff2c3c0cd6f26b942f3c73a35031b9ecb4d82418a52892dabb459b27f0ba04af5e90636edf0b2caaa2d7906a",
      [105] = "3b6dd73c9552f2381107bf206b49c7967fdc5f5011d877d9c576bb4da6d74fbbabf46a1105242d7c645978e54c0b44adaf06d9f7aa4703e8a58829f6d87c5168",
      [106] = "470edb01e9dc9db187acdc9fa594e35b40831f9ddf76309d4a99a7aef1f0d9f79b5a4c9a22a38aeca3a1c2d6ceaeb603899577a30643a97872717c025a9a4fdc",
      [107] = "8cfcdd655481cca50730fe51ee985e9b51946f1345cb6a1801e5e0ed64ef979f431d5a7c3bd2a479d6d82e354210741956d194ee0febbc132b35907f4e2be32f",
      [108] = "a53d93726f1ba688a57267326473eceddc4ccf992d5c53429ca3edd4b122b4fe0b0568887d65c220cbac93fc4f612f97a09eb95e9f903409c78a22eee4fa1781",
      [109] = "0cda6b04d9466bb7f3995c16732e1347f29c23a64fe0b085fadba0995644cc5aa71587423c274c10e09518310c5f866cfaceb229fabb574219f12182eb114182",
      [110] = "c825949632e509824543f7eaf159fb6041722fce3c1cdcbb613b3d37ff107c519417baac32f8e74fe29d7f4823bf6886956603dca5354a6ed6e4a542e06b7d28",
      [111] = "fa9121c7b32b9e01733d034cfc78cbf67f926c7ed83e82200ef86818196921760b4beff48404df811b953828274461673c68d04e297b0eb7b2b4d60fc6b566a2",
      [112] = "c01d080efd492776a1c43bd23dd99d0a2e626d481e16782e75d54c2503b5dc32bd05f0f1ba33e568b88fd2d970929b719ecbb152f58f130a407c8830604b70ca",
      [113] = "55ddd8ac210a6e18ba1ee055af84c966e0dbff091c43580ae1be703bdb85da31acf6948cf5bd90c55a20e5450f22fb89bd8d0085e39f85a86cc46abbca75e24d",
      [114] = "5e9eb0e4b270d086e77eeaf3ce8b1cfc615031b8c463dc34f5c139786f274f22accb4d89e8f40d1a0c2acc84c4dc0f2bab390a9d9495493bd617ed004271bb64",
      [115] = "eaa30f93760743ac7d0a6cb8ed5ef3b30c59097bc44d0ec337344301deba9fb92b20c488d55de415f6aaed0df4925b42894b81d2e1cde89d91ec7f6cc67262b4",
      [116] = "a8bff469314a1ce0c990bb3fd539d92accb6249cc674b559bc9d3898b7a126fee597197fa42c971443470053c7d7f54b09371a59b0f7af87b1917c5347e8f8e0",
      [117] = "c0c27aea8dbe169c4cf25176cbf12db708fd6303db8cf94a1cfb402c1680d3d68f39bc5b9a10970dd5373cb0fe1cb36fa50e33165140d72933ba87af9d5d1ffe",
      [118] = "d6f856c92a5a694dec299f5a4765bed80e4e7431aa5505f82b21584dd1f1fe970f698bec5a3f4faa593d1aac944a96c21b85463a773cdf3ad87c4a00fb9e5073",
      [119] = "130396a75cb483f2eee8c56d8a668bb3d2641f5243212c0bee2bd33da096ad9eb8179fe18f9eaacf76e09fae9de4c3f14ba13341e345be05bf76c182cc3468cb",
      [120] = "f241de612b01aa2fa3cf01531d2a8e5e17fc761dfd48a704a834a47f57d6eade7804ecc39be42fdef16ec6adeaf7c01c2fd0c4cc97d3860907cfa4a3b36d0c05",
      [121] = "0ae7a79758a9ffbd1c04aa080bfa82daf9641f9c2a1cc82b628cbe4006bd47701c78e5022d2ca5ca5384d26d93fb16d595b9775dab17c88ef38e4ce9fdac4b52",
      [122] = "139de16e90ad012e39f72279140f4f6b12bb93f1cbcffbd1b132f39e7f92822d2b56beafc9ed83a0bf59c5525ffd125b83294b65f51f6e8ebbf85eb1aba85b87",
      [123] = "ccd869ee70892a0f5f3c269b9e21ffc99703855c1c652774febbaf1311bd58c80fb66bc3f747dd98b2f11ad9f5d8311b7ca706d456fc82ccd46bfb01f19e8d87",
      [124] = "77469b56910b022f45f509dcfca04494d8e7978073debf96398cb5a86f31bbe55f2a807a3271b8fe124171416917ab01a87acc7bf005977caaf7b484d87d6a93",
      [125] = "577a80f7cb393ac140af066b524166bb02a8059980b65fd100ecdcbec7721d2d0519a151ae730d4b6d9b97a8e5d2415aa8157856aeae4a7444171ef2a9db252b",
      [126] = "9986e67bf52a755f8924f28dae9627f889a45d466ce8616c4ed68ec3afd7a3a14785c335c6c68d62e7379af762b2bc17117a902083a99fae337a268a5d4f4427",
      [127] = "828613968b501dc00a97e08c73b118aa8876c26b8aac93df128502ab360f91bab50a51e088769a5c1eff4782ace147dce3642554199876374291f5d921629502",
      [128] = "b73d1929aa615934e61a871596b3f3b33359f42b8175602e89f7e06e5f658a243667807ed300314b95cacdd579f3e33abdfbe351909519a846d465c59582f321",
      [129] = "4f681e0bd53cda4b5a2041cc8a06f2eabde44fb16c951fbd5b87702f07aeab611565b19c47fde30587177ebb852e3971bbd8d3fd30da18d71037dfbd98420429",
      [130] = "b2fc6acdce83feb0b9439433915fe5dc1c73af6f17e962d7badd7ad5dd7c5032bc1744855d0ba09da5e4ab1bb1caca3aad8e4a947faa19c4769e128bacfe6b85",
      [131] = "da776a6dc98efb67553dd7867916c5782feba6e8961c878a28cc77fa99620e8417d8ca97941ae9d22bb2949c962221de98e90a18437eaeab66d00eba55d92df9",
      [132] = "d3af4d87de1febdf1b0fdf9012de0788109c2b692a59a3571bddc35b859d7d6cf5aa8aa66f1834a24d3ffed0705aa3e653a978eeb0289f8bab9e5a1aa3533121",
      [133] = "5a3c0664bc599be7686301de9d200c927eef12cb0daace1a8b540b63e3d7e0a1591aac7f87699b31bb1af24410d7ab18d0b258bc399256c25e213466e6d18420",
      [134] = "dd5ff1c06a5c050e778a691568814b4db5f09682b40636ea9e13c0552a513e49241934f1027b774b81e8aba4cced4f55c2124eb1dccae7e5c9fb09d9c7206a3e",
      [135] = "018305457c1804285649e77d1ada038a4db3b166a39dc93504584bbb9f95be2d5a2147798aa71d0f240f442d2daf4928695548cf828c7fe314149544b442fb7c",
      [136] = "389860167dc973108096b0c37276b4d62dd707c9826651318ad560af1daf234376f49e95419d310e9c5095d439f6d16e978e848d1951b1586dec6e0aaa84e61c",
      [137] = "1d91d9f1934334408937ab161416f6276975c50cc980c6fdd332496c5c0ec29f62baac0b2c0acbf8e57336acf93c1e3172eb6c627a02679b419a90acc7c8a65f",
      [138] = "a93449912b83c925b3b66af530994a565164870d4d1c779c97392d6438337d5807e5f366ce4ba5e9ea16ceb490b8bb3eb001bf4f513a463e0f01e56e2ff8a3ed",
      [139] = "884040104d933d47e61bff06f458db489f43a823baa14f3e54bc04e9a8edbb38c36a1e81f122a9dd727efcfa9f9dcb70f765c9b70f215e6b63103b4ef830444c",
      [140] = "bb1d3fa26d5432447589030b9fb510b306120ec3e50752c4c298e3ab8952523826e10f48344a10dc07e67718c0746032217ad982acc6c4f2b120f529142dcbf7",
   } do
      assert(sha512(("a"):rep(i)) == dgst)
   end

   -- negative byte values
   assert(sha512(("\255"):rep(1e3)) == "4f598854fd3db77c067dfc877450c56f326c03be82384833e01824c4b3187ac38b73fc41d6bd78e9fa8793d6106a1dc1705afb4250d2fa4508ca7b102bdb62d2")

end


local function test_md5()

   local md5 = sha.md5

   assert(md5"" == "d41d8cd98f00b204e9800998ecf8427e")
   assert(md5"a" == "0cc175b9c0f1b6a831c399e269772661")
   assert(md5"abc" == "900150983cd24fb0d6963f7d28e17f72")
   assert(md5"message digest" == "f96b697d7cb7938d525a2f31aaf161d0")
   assert(md5"abcdefghijklmnopqrstuvwxyz" == "c3fcd3d76192e4007dfb496cca67e13b")
   assert(md5"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" == "8215ef0796a20bcaaae116d3876c664a")
   assert(md5"The quick brown fox jumps over the lazy dog" == "9e107d9d372bb6826bd81d3542a419d6")
   assert(md5"The quick brown fox jumps over the lazy dog." == "e4d909c290d0fb1ca068ffaddf22cbd0")
   assert(md5"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789" == "d174ab98d277d9f5a5611c2c9f419d9f")
   assert(md5(("1234567890"):rep(8)) == "57edf4a22be3c955ac49da2e2107b67a")
   assert(md5(("\255"):rep(54)) == "30855eb73c2f88ffc3005b998ca4cd69")
   assert(md5(("\255"):rep(55)) == "fd696aa639acaba9ce0e0964028fbe81")
   assert(md5(("\255"):rep(56)) == "74444b7e7b01632f3277365c8ca35ec2")

end


local function test_sha1()

   local sha1 = sha.sha1

   assert(sha1"" == "da39a3ee5e6b4b0d3255bfef95601890afd80709")
   assert(sha1"abc" == "a9993e364706816aba3e25717850c26c9cd0d89d")
   assert(sha1"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" == "84983e441c3bd26ebaae4aa1f95129e5e54670f1")
   assert(sha1"The quick brown fox jumps over the lazy dog" == "2fd4e1c67a2d28fced849ee1bb76e7391b93eb12")
   assert(sha1"The quick brown fox jumps over the lazy cog" == "de9f2c7fd25e1b3afad3e85a0bd17d9b100db4b3")

end


local function test_sha3()

   assert(sha.sha3_224"" == "6b4e03423667dbb73b6e15454f0eb1abd4597f9a1b078e3f5b5a6bc7")
   assert(sha.sha3_256"" == "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a")
   assert(sha.sha3_384"" == "0c63a75b845e4f7d01107d852e4c2485c51a50aaaa94fc61995e71bbee983a2ac3713831264adb47fb6bd1e058d5f004")
   assert(sha.sha3_512"" == "a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a615b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26")
   assert(sha.sha3_224"The quick brown fox jumps over the lazy dog" == "d15dadceaa4d5d7bb3b48f446421d542e08ad8887305e28d58335795")
   assert(sha.sha3_256"The quick brown fox jumps over the lazy dog" == "69070dda01975c8c120c3aada1b282394e7f032fa9cf32f4cb2259a0897dfc04")
   assert(sha.sha3_384"The quick brown fox jumps over the lazy dog" == "7063465e08a93bce31cd89d2e3ca8f602498696e253592ed26f07bf7e703cf328581e1471a7ba7ab119b1a9ebdf8be41")
   assert(sha.sha3_512"The quick brown fox jumps over the lazy dog" == "01dedd5de4ef14642445ba5f5b97c15e47b9ad931326e4b0727cd94cefc44fff23f07bf543139939b49128caf436dc1bdee54fcb24023a08d9403f9b4bf0d450")
   assert(sha.shake256(64, "") == "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762fd75dc4ddd8c0f200cb05019d67b592f6fc821c49479ab48640292eacb3b7c4be")
   assert(sha.shake256(25, ("€"):rep(45))  == "8f571c3d042d43f9072941f81862e34b7127cae59edc8092e7")      -- input data is 1 byte less than block size
   assert(sha.shake256(26, ("€"):rep(90))  == "ea57f4ed3404c1a2a3f19d706cbc0971665104b49f8aea5569a2")    -- input data is 2 bytes less than two blocks
   assert(sha.shake256(27, ("€"):rep(136)) == "8c1fe6c7831770ee3c5738f2ebfddff126e71e798daf26c0735a2f")  -- input data is exactly three blocks
   assert(sha.shake256(150, "The quick brown fox jumps over the lazy dog") == "2f671343d9b2e1604dc9dcf0753e5fe15c7c64a0d283cbbf722d411a0e36f6ca1d01d1369a23539cd80f7c054b6e5daf9c962cad5b8ed5bd11998b40d5734442bed798f6e5c915bd8bb07e0188d0a55c1290074f1c287af06352299184492cbdec9acba737ee292e5adaa445547355e72a03a3bac3aac770fe5d6b66600ff15d37d5b4789994ea2aeb097f550aa5e88e4d8ff0ba07b8")
   assert(sha.shake128(32, "") == "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26")
   assert(sha.shake128(32, "The quick brown fox jumps over the lazy dof") == "853f4538be0db9621a6cea659a06c1107b1f83f02b13d18297bd39d7411cf10c")
   assert(sha.shake128(32, "The quick brown fox jumps over the lazy dog") == "f4202e3c5852f9182a0430fd8144f0a74b95e7417ecae17db0f8cfeed0e3e66e")
   assert(sha.shake128(12, "The quick brown fox jumps over the lazy dog") == "f4202e3c5852f9182a0430fd")
   assert(sha.shake128(11, "The quick brown fox jumps over the lazy dog") == "f4202e3c5852f9182a0430")

   local append_input_message = sha.shake128(7)
   append_input_message("The quick brown fox")
   append_input_message(" jumps over")
   append_input_message(" the lazy dog")
   assert(append_input_message() == "f4202e3c5852f9")

   -- digest_size_in_bytes == (-1) means "generate infinite SHAKE-stream instead of fixed-width digest"
   local get_next_part_of_digest = sha.shake128(-1, "The quick brown fox jumps over the lazy dog")
   assert(get_next_part_of_digest(5) == "f4202e3c58") -- 5 bytes in hexadecimal representation
   assert(get_next_part_of_digest()  == "52")         -- size=1 is assumed when omitted
   assert(get_next_part_of_digest(0) == "")           -- size=0 is a valid size
   assert(get_next_part_of_digest(4) == "f9182a04")   -- and so on to the infinity...

   -- take long message (in chunk-by-chunk mode) and generate infinite SHAKE-stream
   local append_input_message = sha.shake128(-1)
   append_input_message("The quick brown fox")
   append_input_message(" jumps over the lazy dog")
   local get_next_part_of_digest = append_input_message()  -- input stream is terminated, now starting to receive the output stream
   assert(get_next_part_of_digest(5) == "f4202e3c58")      -- 5 bytes in hexadecimal representation
   assert(get_next_part_of_digest(5) == "52f9182a04")      -- and so on to the infinity...

   -- useless special case: digest of length 0
   assert(sha.shake128(0, "The quick brown fox jumps over the lazy dog") == "")
   local append_input_message = sha.shake128(0)
   append_input_message("The quick brown fox")
   append_input_message(" jumps over the lazy dog")
   assert(append_input_message() == "")

end


local function test_blake2()

   -- Test BLAKE2b
   assert(sha.blake2b_384("") == "b32811423377f52d7862286ee1a72ee540524380fda1724a6f25d7978c6fd3244a6caf0498812673c5e05ef583825100")
   assert(sha.blake2b_512("") == "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce")
   assert(sha.blake2b("The quick brown fox jumps over the lazy dog") == "a8add4bdddfd93e4877d2746e62817b116364a1fa7bc148d95090bc7333b3673f82401cf7aa2e4cb1ecd90296e3f14cb5413f8ed77be73045b13914cdcd6a918")
   assert(sha.blake2b("The quick brown fox jumps over the lazy dof") == "ab6b007747d8068c02e25a6008db8a77c218d94f3b40d2291a7dc8a62090a744c082ea27af01521a102e42f480a31e9844053f456b4b41e8aa78bbe5c12957bb")
   assert(sha.blake2b("message") == "7bd9044c67faf33ba5cd8ae162680cd9d7a8d3180b15b39952737b8572dfced52b559acd6aa7f8c833a1b3172bd2771683c793c772d4abe3dd9bd9f63c204701")
   assert(sha.blake2b("message", "key") == "550d438c7cd4e1861c529cf87c953e28370a62b11df72caf642bdd4b9fbef7997fdfe5db511d51c331260799fc68d4ce15ebe934498a494af9e77d4c88fb3efd")
   assert(sha.blake2b("message", nil, "salt") == "416397711dc3785cb45f41678647ba9e3494f6cfaa4f92c3de7bf846fc389ee966daa972c6e0b441f4dd49ada1a52988dd24359fffcbb3469e29b29298a51ab8")
   assert(sha.blake2b("message", "key", "salt") == "478c73516862923a4780520ac2236d38db45e26832e3f1a2440dddfeea3aea04ddbd0f2b3e48c680961f1d22e2c4428114d14f8afbd9bc3fc173b5507f1cab1f")
   assert(sha.blake2b(("€"):rep(100)) == "f43189d7a60c822551415b8340c40cb6606581cb66bc48a9be4108fe7d8a4bbdefd7e5c72fe1526d8170ad068cb15b578348f01a8972020cb5c1207a23d6e134")
   assert(sha.blake2b(("€"):rep(100), "100 euro") == "fcb4e39c94cc0a336570b6d0594c9d8110e598ada639705af8a6f5089dcb90a91846c6b0b4755fe86b6242c604a09c61f72590a2664a98e226748516d757f014")
   do
      local s = "my salt"           assert(#s <= 16)  -- "Salt" field
      local p = "my personalizati"  assert(#p <= 16)  -- "Personalization" field
      local salt = s..("\0"):rep(16-#s)..p            -- concatenation of "Salt" + "Personalization" fields
      assert(sha.blake2b("my message", "my key", salt) == "9268e178f82c0980033ba4e6f7056612f2c37b8244601363cfa8f8ff959bab4e790fcb47afa0bd1142f69e9d61e4babd62b291eba57c521ae6d349b11b48a2e0")
   end
   assert(sha.blake2b(("\255"):rep(999), ("\255"):rep(64), ("\255"):rep(32)) == "0d8a6a5cf6e59853213d760fbc5cb66313e1d5182aecf9dc9eafe04f96e7888f0222940a57f937b353068f2a571e778769c6a840635738a86d234925cbd11e42")
   assert(sha.blake2b(("\128"):rep(17), ("\128"):rep(17), ("\128"):rep(17)) == "47a679b056586be8f60346749e996c8c6e83ae8fc7e89a71fb0954c8e3a4b326d157082457390468b82ff048231c8ef5a8cd4ad0929800dcfd2e344f19409d26")
   assert(sha.blake2b(("\128"):rep(9), ("\128"):rep(9), ("\128"):rep(9)) == "9739afd1184492ca2ac8e223d050981258d5739627762cbd64f06f5b0cb827522d13ee1b229f2ab660b554e59a6e25bea5c4a3633cf4703dcf998e5f211f48b4")
   assert(sha.blake2b("your message", "your key") == "feee3e3aac7d5a3a4653fb70667ad6fb5fafe5256c78867b421eb0ce4134fc62784002b261056c4ef4222e99a8944826dff6f4845ac0117df128de116b159d75")
   local append = sha.blake2b(nil, "your key")
   append("your")
   append(" message")
   assert(append() == "feee3e3aac7d5a3a4653fb70667ad6fb5fafe5256c78867b421eb0ce4134fc62784002b261056c4ef4222e99a8944826dff6f4845ac0117df128de116b159d75")

   -- Test BLAKE2s
   assert(sha.blake2s_224("") == "1fa1291e65248b37b3433475b2a0dd63d54a11ecc4e3e034e7bc1ef4")
   assert(sha.blake2s_256("") == "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9")
   assert(sha.blake2s("message") == "e6d7039c6d8c2ae1706e2cd3d2684e59d8b86ea9d21273a1e06263932ea367a4")
   assert(sha.blake2s("message", "key") == "6167e07bf13af66076d94c1f6e395ee73b647d4c7013238d63808e805ae3ae59")
   assert(sha.blake2s("message", nil, "salt") == "21faaaeeaa27906aa5465510b6640cb383d536ef6a1ef9e2b91fc4beccb1dcd0")
   assert(sha.blake2s("message", "key", "salt") == "9953f155c11cb98eb4a62db577dc2ff6ff6c1a7b36c2b5ad3274f202bea23d67")
   assert(sha.blake2s(("€"):rep(100)) == "d58876a6350bb985155de324df9239fa241b3bc80517d88282f19aaf77701eba")
   assert(sha.blake2s(("€"):rep(100), "100 euro") == "9e54259e2ff40c09dbbed369e4c5a01a150ec01e31cb0565a2a445dcf9bf279d")
   do
      local s = "my salt"   assert(#s <= 8)  -- "Salt" field
      local p = "my pers"   assert(#p <= 8)  -- "Personalization" field
      local salt = s..("\0"):rep(8-#s)..p    -- concatenation of "Salt" + "Personalization" fields
      assert(sha.blake2s("my message", "my key", salt) == "96d9b162046d282b81a651dcd5d49df05f67f6617bb56ad28cad22a7c1040bc8")
   end
   assert(sha.blake2s(("\255"):rep(999), ("\255"):rep(32), ("\255"):rep(16)) == "2502074ea85b4eb732c4296c82c662371ed80ca962920e0b6169030bf4633228")

   -- Test BLAKE2bp
   assert(sha.blake2bp("message") == "9cf494d3adfa1c639280b7e2101de182014fc142aec93d5a31c54c608158335e993a8955bf6f062e0669cad9ebdcdd0144da168460745528cb2a49c9528256a3")
   assert(sha.blake2bp("message", "key") == "aeb49f2817db0ef5910fec836272de7be819a6017920dd6d94d9380b16f24d5d5c930adc6d147cc12dae984fbbc0379c4a333c98a28f2beb942752dca49838c5")
   assert(sha.blake2bp("message", nil, "salt") == "b093b4ee84640dfe06a5eb21a0411b788d675c91b898a9efb5da4f819c54d2135a1d939af1f4b3b2fefea53cfa1ed77d2ef102ed19a65118593161a058e27a9f")
   assert(sha.blake2bp("message", "key", "salt") == "bf71085230daaffdfadd3e2d745f733c3a7000a507a681b46198697f43cba7ae0c9f17b1231434a445f46734b5e21d51223d4760886a5fb5784a181d85f9bc53")

   -- Test BLAKE2sp
   assert(sha.blake2sp("message") == "c278b6c68e2ecfa36434c65acfec9076d797a1449d104ac454df200b8a429a96")
   assert(sha.blake2sp("message", "key") == "09fd315f5347107d9b94de22f2abe2f358d029c0294c2b577f285c7b0c01d1db")
   assert(sha.blake2sp("message", nil, "salt") == "5a93b13e04ac708d0bf1a1f855f32ff6eb8f9716a36cd18d5f1a5cdc89c8656e")
   assert(sha.blake2sp("message", "key", "salt") == "d2b13f23784e5904967d0a94913523c9657b3e4c57c858217bf0074afbf895d3")
   -- Want more test vectors for BLAKE2sp? You can get BLAKE2sp hash sum (no key, no salt) of any file using 7-Zip or RAR:
   --    7-Zip (version 15.06+):
   --       7z h -scrcblake2sp YOUR_FILE
   --    RAR (version 5.0+):
   --       rar a -m0 -ma -htb -inul tmp.rar YOUR_FILE && rar lt tmp.rar && rm tmp.rar
   --       (for Windows users: replace "rm" with "del")

   -- Test BLAKE2Xb
   assert(sha.blake2xb(65, "message") == "90aa97980b876527d78da8639d91419b76a6cb93aa2bccf7ef69603c3b37a9c7c708662540400c523e304a7f50a65d64eb0d16a295d2e33a97455e958c73efc2c7")
   assert(sha.blake2xb(65, "message", "key") == "2fcf18805eec564af2e24c5493b9038b1f652900b413b85d5f1b92ee4f281792ff2592657d915c4800d3ca026a47c4ec3692134a28a1f8d6cc310708bdfb501e46")
   assert(sha.blake2xb(65, "message", nil, "salt") == "2885f976dd6eeb7253d0cd3dce63a5d8ab480d3288ef193b7bad722fe914f382ab3b929709f9370290222d06e133e047a6d8d8f09d46fa0f0961bedb3f55d74be5")
   assert(sha.blake2xb(65, "message", "key", "salt") == "088dfd13d5cbab9505ae2e0d281bc1ca95dd74c0a00c021e1ffe63532a88ce43578fac63d99a596460af0d52ccbba21d2d7667384f3feff82a0507e4fc1180a6de")
   local get_next_part_of_digest = sha.blake2xb(-16 * 2^20, "The quick brown fox jumps over the lazy dog")
   assert(get_next_part_of_digest(5) == "53e2dcdfe2")
   assert(get_next_part_of_digest()  == "1b")
   assert(get_next_part_of_digest(0) == "")
   assert(get_next_part_of_digest(3) == "21af5b")
   get_next_part_of_digest("seek", 16 * 2^20 - 5)
   assert(get_next_part_of_digest(5) == "b2b5312606")
   assert(get_next_part_of_digest(1) == "")
   get_next_part_of_digest("seek", 16 * 2^20 - 5)
   assert(get_next_part_of_digest(555) == "b2b5312606")
   get_next_part_of_digest("seek", -10)
   assert(get_next_part_of_digest(15) == "53e2dcdfe2")
   local append_input_message = sha.blake2xb(-16 * 2^20)
   append_input_message("The quick brown fox")
   append_input_message(" jumps over the lazy dog")
   local get_next_part_of_digest = append_input_message()
   assert(get_next_part_of_digest(4) == "53e2dcdf")
   assert(get_next_part_of_digest(4) == "e21b21af")
   local get_next_part_of_digest = sha.blake2xb(-1, "The quick brown fox jumps over the lazy dog")
   assert(get_next_part_of_digest(5) == "364e84ca4c")
   assert(get_next_part_of_digest(5) == "103df29230")
   get_next_part_of_digest("seek", 10*2^30)
   assert(get_next_part_of_digest(5) == "eeafce070f")
   get_next_part_of_digest("seek", 0)
   assert(get_next_part_of_digest(5.0) == "364e84ca4c")
   get_next_part_of_digest("seek", 1)
   assert(get_next_part_of_digest(5) == "4e84ca4c10")
   get_next_part_of_digest("seek", -10)
   assert(get_next_part_of_digest(20) == "5538642bb3ddedba69a4364e84ca4c103df29230")
   get_next_part_of_digest("seek", 2^31-10)
   assert(get_next_part_of_digest(20) == "e2a4267324dd36006f3a985f88b74111f494a73c")
   get_next_part_of_digest("seek", 2^32-10)
   assert(get_next_part_of_digest(20) == "d13c13778d4e4b59044c8a6126261b814814c280")
   get_next_part_of_digest("seek", 64*2^31-10)
   assert(get_next_part_of_digest(20) == "f638601af5aa9bac8b5f0ee69ee2970ff68cd3a3")
   get_next_part_of_digest("seek", 64*2^32-10)
   assert(get_next_part_of_digest(20) == "5538642bb3ddedba69a4364e84ca4c103df29230")

   -- Test BLAKE2Xs
   assert(sha.blake2xs(33, "message") == "a738fcffa5c656eebb0e7dc46fd8eafff960dcb46d36cb2896b444bfbbd623f910")
   assert(sha.blake2xs(33, "message", "key") == "a7d460f42db67f6f07d85ae346ec5dba41ca056e67a366cef583f36f9e3d969d52")
   assert(sha.blake2xs(33, "message", nil, "salt") == "8370c1b120c6ae76a5cdbf24bf8c082ed3d647127726f5da85a1c1ffd29e35335c")
   assert(sha.blake2xs(33, "message", "key", "salt") == "f5d6f28e3720d789c847b65e2f1113792e6ac4da59fa653c10f3b0a9304021d7a1")
   assert(sha.blake2xs(132, "your string") == "4fae7a4abcf47aec81991c370e8c716adc5bf7a142e932fc18b50d325f5ca7059fe7369fb86088b253dcbec9ff9fd168d5a229e507c9d984e9e8c0e1fa27824b51de5af9323594f0decd317ad3ed54aac7e5f816728fb39f7c3df873479f9063188566b788150a0dfaded9f06cf45aa1ef1bb80451e8f4dc8554ae790797188dce0e13fa")
   local get_next_part_of_digest = sha.blake2xs(-1, "The quick brown fox jumps over the lazy dog")
   assert(get_next_part_of_digest(10) == "0650cde4df888a06eada")
   get_next_part_of_digest("seek", -10)
   assert(get_next_part_of_digest(20) == "d2b24a4e7e4d924cfbe30650cde4df888a06eada")
   get_next_part_of_digest("seek", 2^31-10)
   assert(get_next_part_of_digest(20) == "c635d7a48f65efe8c65e65e076f41ad64504f6d1")
   get_next_part_of_digest("seek", 2^32-10)
   assert(get_next_part_of_digest(20) == "f9c9378e8778ce71d78e77c378116835376b1c46")
   get_next_part_of_digest("seek", 32*2^31-10)
   assert(get_next_part_of_digest(20) == "1ba18817e49f0319f7ef07da100f3419bc4db148")
   get_next_part_of_digest("seek", 32*2^32-10)
   assert(get_next_part_of_digest(20) == "d2b24a4e7e4d924cfbe30650cde4df888a06eada")

   -- useless special case: digest of length 0
   assert(sha.blake2xs(0, "The quick brown fox jumps over the lazy dog") == "")
   local append_input_message = sha.blake2xs(0)  -- "chunk-by-chunk" input mode
   append_input_message("The quick brown fox")
   append_input_message(" jumps over the lazy dog")
   assert(append_input_message() == "")

end


local function test_blake3()

   -- test vectors published by BLAKE3 authors
   do
      local test_vectors = [[
         {
           "input_len": 0,
           "hash": "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262e00f03e7b69af26b7faaf09fcd333050338ddfe085b8cc869ca98b206c08243a26f5487789e8f660afe6c99ef9e0c52b92e7393024a80459cf91f476f9ffdbda7001c22e159b402631f277ca96f2defdf1078282314e763699a31c5363165421cce14d",
           "keyed_hash": "92b2b75604ed3c761f9d6f62392c8a9227ad0ea3f09573e783f1498a4ed60d26b18171a2f22a4b94822c701f107153dba24918c4bae4d2945c20ece13387627d3b73cbf97b797d5e59948c7ef788f54372df45e45e4293c7dc18c1d41144a9758be58960856be1eabbe22c2653190de560ca3b2ac4aa692a9210694254c371e851bc8f",
           "derive_key": "2cc39783c223154fea8dfb7c1b1660f2ac2dcbd1c1de8277b0b0dd39b7e50d7d905630c8be290dfcf3e6842f13bddd573c098c3f17361f1f206b8cad9d088aa4a3f746752c6b0ce6a83b0da81d59649257cdf8eb3e9f7d4998e41021fac119deefb896224ac99f860011f73609e6e0e4540f93b273e56547dfd3aa1a035ba6689d89a0"
         },
         {
           "input_len": 1,
           "hash": "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213c3a6cb8bf623e20cdb535f8d1a5ffb86342d9c0b64aca3bce1d31f60adfa137b358ad4d79f97b47c3d5e79f179df87a3b9776ef8325f8329886ba42f07fb138bb502f4081cbcec3195c5871e6c23e2cc97d3c69a613eba131e5f1351f3f1da786545e5",
           "keyed_hash": "6d7878dfff2f485635d39013278ae14f1454b8c0a3a2d34bc1ab38228a80c95b6568c0490609413006fbd428eb3fd14e7756d90f73a4725fad147f7bf70fd61c4e0cf7074885e92b0e3f125978b4154986d4fb202a3f331a3fb6cf349a3a70e49990f98fe4289761c8602c4e6ab1138d31d3b62218078b2f3ba9a88e1d08d0dd4cea11",
           "derive_key": "b3e2e340a117a499c6cf2398a19ee0d29cca2bb7404c73063382693bf66cb06c5827b91bf889b6b97c5477f535361caefca0b5d8c4746441c57617111933158950670f9aa8a05d791daae10ac683cbef8faf897c84e6114a59d2173c3f417023a35d6983f2c7dfa57e7fc559ad751dbfb9ffab39c2ef8c4aafebc9ae973a64f0c76551"
         },
         {
           "input_len": 2,
           "hash": "7b7015bb92cf0b318037702a6cdd81dee41224f734684c2c122cd6359cb1ee63d8386b22e2ddc05836b7c1bb693d92af006deb5ffbc4c70fb44d0195d0c6f252faac61659ef86523aa16517f87cb5f1340e723756ab65efb2f91964e14391de2a432263a6faf1d146937b35a33621c12d00be8223a7f1919cec0acd12097ff3ab00ab1",
           "keyed_hash": "5392ddae0e0a69d5f40160462cbd9bd889375082ff224ac9c758802b7a6fd20a9ffbf7efd13e989a6c246f96d3a96b9d279f2c4e63fb0bdff633957acf50ee1a5f658be144bab0f6f16500dee4aa5967fc2c586d85a04caddec90fffb7633f46a60786024353b9e5cebe277fcd9514217fee2267dcda8f7b31697b7c54fab6a939bf8f",
           "derive_key": "1f166565a7df0098ee65922d7fea425fb18b9943f19d6161e2d17939356168e6daa59cae19892b2d54f6fc9f475d26031fd1c22ae0a3e8ef7bdb23f452a15e0027629d2e867b1bb1e6ab21c71297377750826c404dfccc2406bd57a83775f89e0b075e59a7732326715ef912078e213944f490ad68037557518b79c0086de6d6f6cdd2"
         },
         {
           "input_len": 3,
           "hash": "e1be4d7a8ab5560aa4199eea339849ba8e293d55ca0a81006726d184519e647f5b49b82f805a538c68915c1ae8035c900fd1d4b13902920fd05e1450822f36de9454b7e9996de4900c8e723512883f93f4345f8a58bfe64ee38d3ad71ab027765d25cdd0e448328a8e7a683b9a6af8b0af94fa09010d9186890b096a08471e4230a134",
           "keyed_hash": "39e67b76b5a007d4921969779fe666da67b5213b096084ab674742f0d5ec62b9b9142d0fab08e1b161efdbb28d18afc64d8f72160c958e53a950cdecf91c1a1bbab1a9c0f01def762a77e2e8545d4dec241e98a89b6db2e9a5b070fc110caae2622690bd7b76c02ab60750a3ea75426a6bb8803c370ffe465f07fb57def95df772c39f",
           "derive_key": "440aba35cb006b61fc17c0529255de438efc06a8c9ebf3f2ddac3b5a86705797f27e2e914574f4d87ec04c379e12789eccbfbc15892626042707802dbe4e97c3ff59dca80c1e54246b6d055154f7348a39b7d098b2b4824ebe90e104e763b2a447512132cede16243484a55a4e40a85790038bb0dcf762e8c053cabae41bbe22a5bff7"
         },
         {
           "input_len": 4,
           "hash": "f30f5ab28fe047904037f77b6da4fea1e27241c5d132638d8bedce9d40494f328f603ba4564453e06cdcee6cbe728a4519bbe6f0d41e8a14b5b225174a566dbfa61b56afb1e452dc08c804f8c3143c9e2cc4a31bb738bf8c1917b55830c6e65797211701dc0b98daa1faeaa6ee9e56ab606ce03a1a881e8f14e87a4acf4646272cfd12",
           "keyed_hash": "7671dde590c95d5ac9616651ff5aa0a27bee5913a348e053b8aa9108917fe070116c0acff3f0d1fa97ab38d813fd46506089118147d83393019b068a55d646251ecf81105f798d76a10ae413f3d925787d6216a7eb444e510fd56916f1d753a5544ecf0072134a146b2615b42f50c179f56b8fae0788008e3e27c67482349e249cb86a",
           "derive_key": "f46085c8190d69022369ce1a18880e9b369c135eb93f3c63550d3e7630e91060fbd7d8f4258bec9da4e05044f88b91944f7cab317a2f0c18279629a3867fad0662c9ad4d42c6f27e5b124da17c8c4f3a94a025ba5d1b623686c6099d202a7317a82e3d95dae46a87de0555d727a5df55de44dab799a20dffe239594d6e99ed17950910"
         },
         {
           "input_len": 5,
           "hash": "b40b44dfd97e7a84a996a91af8b85188c66c126940ba7aad2e7ae6b385402aa2ebcfdac6c5d32c31209e1f81a454751280db64942ce395104e1e4eaca62607de1c2ca748251754ea5bbe8c20150e7f47efd57012c63b3c6a6632dc1c7cd15f3e1c999904037d60fac2eb9397f2adbe458d7f264e64f1e73aa927b30988e2aed2f03620",
           "keyed_hash": "73ac69eecf286894d8102018a6fc729f4b1f4247d3703f69bdc6a5fe3e0c84616ab199d1f2f3e53bffb17f0a2209fe8b4f7d4c7bae59c2bc7d01f1ff94c67588cc6b38fa6024886f2c078bfe09b5d9e6584cd6c521c3bb52f4de7687b37117a2dbbec0d59e92fa9a8cc3240d4432f91757aabcae03e87431dac003e7d73574bfdd8218",
           "derive_key": "1f24eda69dbcb752847ec3ebb5dd42836d86e58500c7c98d906ecd82ed9ae47f6f48a3f67e4e43329c9a89b1ca526b9b35cbf7d25c1e353baffb590fd79be58ddb6c711f1a6b60e98620b851c688670412fcb0435657ba6b638d21f0f2a04f2f6b0bd8834837b10e438d5f4c7c2c71299cf7586ea9144ed09253d51f8f54dd6bff719d"
         },
         {
           "input_len": 6,
           "hash": "06c4e8ffb6872fad96f9aaca5eee1553eb62aed0ad7198cef42e87f6a616c844611a30c4e4f37fe2fe23c0883cde5cf7059d88b657c7ed2087e3d210925ede716435d6d5d82597a1e52b9553919e804f5656278bd739880692c94bff2824d8e0b48cac1d24682699e4883389dc4f2faa2eb3b4db6e39debd5061ff3609916f3e07529a",
           "keyed_hash": "82d3199d0013035682cc7f2a399d4c212544376a839aa863a0f4c91220ca7a6dc2ffb3aa05f2631f0fa9ac19b6e97eb7e6669e5ec254799350c8b8d189e8807800842a5383c4d907c932f34490aaf00064de8cdb157357bde37c1504d2960034930887603abc5ccb9f5247f79224baff6120a3c622a46d7b1bcaee02c5025460941256",
           "derive_key": "be96b30b37919fe4379dfbe752ae77b4f7e2ab92f7ff27435f76f2f065f6a5f435ae01a1d14bd5a6b3b69d8cbd35f0b01ef2173ff6f9b640ca0bd4748efa398bf9a9c0acd6a66d9332fdc9b47ffe28ba7ab6090c26747b85f4fab22f936b71eb3f64613d8bd9dfabe9bb68da19de78321b481e5297df9e40ec8a3d662f3e1479c65de0"
         },
         {
           "input_len": 7,
           "hash": "3f8770f387faad08faa9d8414e9f449ac68e6ff0417f673f602a646a891419fe66036ef6e6d1a8f54baa9fed1fc11c77cfb9cff65bae915045027046ebe0c01bf5a941f3bb0f73791d3fc0b84370f9f30af0cd5b0fc334dd61f70feb60dad785f070fef1f343ed933b49a5ca0d16a503f599a365a4296739248b28d1a20b0e2cc8975c",
           "keyed_hash": "af0a7ec382aedc0cfd626e49e7628bc7a353a4cb108855541a5651bf64fbb28a7c5035ba0f48a9c73dabb2be0533d02e8fd5d0d5639a18b2803ba6bf527e1d145d5fd6406c437b79bcaad6c7bdf1cf4bd56a893c3eb9510335a7a798548c6753f74617bede88bef924ba4b334f8852476d90b26c5dc4c3668a2519266a562c6c8034a6",
           "derive_key": "dc3b6485f9d94935329442916b0d059685ba815a1fa2a14107217453a7fc9f0e66266db2ea7c96843f9d8208e600a73f7f45b2f55b9e6d6a7ccf05daae63a3fdd10b25ac0bd2e224ce8291f88c05976d575df998477db86fb2cfbbf91725d62cb57acfeb3c2d973b89b503c2b60dde85a7802b69dc1ac2007d5623cbea8cbfb6b181f5"
         },
         {
           "input_len": 8,
           "hash": "2351207d04fc16ade43ccab08600939c7c1fa70a5c0aaca76063d04c3228eaeb725d6d46ceed8f785ab9f2f9b06acfe398c6699c6129da084cb531177445a682894f9685eaf836999221d17c9a64a3a057000524cd2823986db378b074290a1a9b93a22e135ed2c14c7e20c6d045cd00b903400374126676ea78874d79f2dd7883cf5c",
           "keyed_hash": "be2f5495c61cba1bb348a34948c004045e3bd4dae8f0fe82bf44d0da245a060048eb5e68ce6dea1eb0229e144f578b3aa7e9f4f85febd135df8525e6fe40c6f0340d13dd09b255ccd5112a94238f2be3c0b5b7ecde06580426a93e0708555a265305abf86d874e34b4995b788e37a823491f25127a502fe0704baa6bfdf04e76c13276",
           "derive_key": "2b166978cef14d9d438046c720519d8b1cad707e199746f1562d0c87fbd32940f0e2545a96693a66654225ebbaac76d093bfa9cd8f525a53acb92a861a98c42e7d1c4ae82e68ab691d510012edd2a728f98cd4794ef757e94d6546961b4f280a51aac339cc95b64a92b83cc3f26d8af8dfb4c091c240acdb4d47728d23e7148720ef04"
         },
         {
           "input_len": 63,
           "hash": "e9bc37a594daad83be9470df7f7b3798297c3d834ce80ba85d6e207627b7db7b1197012b1e7d9af4d7cb7bdd1f3bb49a90a9b5dec3ea2bbc6eaebce77f4e470cbf4687093b5352f04e4a4570fba233164e6acc36900e35d185886a827f7ea9bdc1e5c3ce88b095a200e62c10c043b3e9bc6cb9b6ac4dfa51794b02ace9f98779040755",
           "keyed_hash": "bb1eb5d4afa793c1ebdd9fb08def6c36d10096986ae0cfe148cd101170ce37aea05a63d74a840aecd514f654f080e51ac50fd617d22610d91780fe6b07a26b0847abb38291058c97474ef6ddd190d30fc318185c09ca1589d2024f0a6f16d45f11678377483fa5c005b2a107cb9943e5da634e7046855eaa888663de55d6471371d55d",
           "derive_key": "b6451e30b953c206e34644c6803724e9d2725e0893039cfc49584f991f451af3b89e8ff572d3da4f4022199b9563b9d70ebb616efff0763e9abec71b550f1371e233319c4c4e74da936ba8e5bbb29a598e007a0bbfa929c99738ca2cc098d59134d11ff300c39f82e2fce9f7f0fa266459503f64ab9913befc65fddc474f6dc1c67669"
         },
         {
           "input_len": 64,
           "hash": "4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98fc9cc56cb831ffe33ea8e7e1d1df09b26efd2767670066aa82d023b1dfe8ab1b2b7fbb5b97592d46ffe3e05a6a9b592e2949c74160e4674301bc3f97e04903f8c6cf95b863174c33228924cdef7ae47559b10b294acd660666c4538833582b43f82d74",
           "keyed_hash": "ba8ced36f327700d213f120b1a207a3b8c04330528586f414d09f2f7d9ccb7e68244c26010afc3f762615bbac552a1ca909e67c83e2fd5478cf46b9e811efccc93f77a21b17a152ebaca1695733fdb086e23cd0eb48c41c034d52523fc21236e5d8c9255306e48d52ba40b4dac24256460d56573d1312319afcf3ed39d72d0bfc69acb",
           "derive_key": "a5c4a7053fa86b64746d4bb688d06ad1f02a18fce9afd3e818fefaa7126bf73e9b9493a9befebe0bf0c9509fb3105cfa0e262cde141aa8e3f2c2f77890bb64a4cca96922a21ead111f6338ad5244f2c15c44cb595443ac2ac294231e31be4a4307d0a91e874d36fc9852aeb1265c09b6e0cda7c37ef686fbbcab97e8ff66718be048bb"
         },
         {
           "input_len": 65,
           "hash": "de1e5fa0be70df6d2be8fffd0e99ceaa8eb6e8c93a63f2d8d1c30ecb6b263dee0e16e0a4749d6811dd1d6d1265c29729b1b75a9ac346cf93f0e1d7296dfcfd4313b3a227faaaaf7757cc95b4e87a49be3b8a270a12020233509b1c3632b3485eef309d0abc4a4a696c9decc6e90454b53b000f456a3f10079072baaf7a981653221f2c",
           "keyed_hash": "c0a4edefa2d2accb9277c371ac12fcdbb52988a86edc54f0716e1591b4326e72d5e795f46a596b02d3d4bfb43abad1e5d19211152722ec1f20fef2cd413e3c22f2fc5da3d73041275be6ede3517b3b9f0fc67ade5956a672b8b75d96cb43294b9041497de92637ed3f2439225e683910cb3ae923374449ca788fb0f9bea92731bc26ad",
           "derive_key": "51fd05c3c1cfbc8ed67d139ad76f5cf8236cd2acd26627a30c104dfd9d3ff8a82b02e8bd36d8498a75ad8c8e9b15eb386970283d6dd42c8ae7911cc592887fdbe26a0a5f0bf821cd92986c60b2502c9be3f98a9c133a7e8045ea867e0828c7252e739321f7c2d65daee4468eb4429efae469a42763f1f94977435d10dccae3e3dce88d"
         },
         {
           "input_len": 127,
           "hash": "d81293fda863f008c09e92fc382a81f5a0b4a1251cba1634016a0f86a6bd640de3137d477156d1fde56b0cf36f8ef18b44b2d79897bece12227539ac9ae0a5119da47644d934d26e74dc316145dcb8bb69ac3f2e05c242dd6ee06484fcb0e956dc44355b452c5e2bbb5e2b66e99f5dd443d0cbcaaafd4beebaed24ae2f8bb672bcef78",
           "keyed_hash": "c64200ae7dfaf35577ac5a9521c47863fb71514a3bcad18819218b818de85818ee7a317aaccc1458f78d6f65f3427ec97d9c0adb0d6dacd4471374b621b7b5f35cd54663c64dbe0b9e2d95632f84c611313ea5bd90b71ce97b3cf645776f3adc11e27d135cbadb9875c2bf8d3ae6b02f8a0206aba0c35bfe42574011931c9a255ce6dc",
           "derive_key": "c91c090ceee3a3ac81902da31838012625bbcd73fcb92e7d7e56f78deba4f0c3feeb3974306966ccb3e3c69c337ef8a45660ad02526306fd685c88542ad00f759af6dd1adc2e50c2b8aac9f0c5221ff481565cf6455b772515a69463223202e5c371743e35210bbbbabd89651684107fd9fe493c937be16e39cfa7084a36207c99bea3"
         },
         {
           "input_len": 128,
           "hash": "f17e570564b26578c33bb7f44643f539624b05df1a76c81f30acd548c44b45efa69faba091427f9c5c4caa873aa07828651f19c55bad85c47d1368b11c6fd99e47ecba5820a0325984d74fe3e4058494ca12e3f1d3293d0010a9722f7dee64f71246f75e9361f44cc8e214a100650db1313ff76a9f93ec6e84edb7add1cb4a95019b0c",
           "keyed_hash": "b04fe15577457267ff3b6f3c947d93be581e7e3a4b018679125eaf86f6a628ecd86bbe0001f10bda47e6077b735016fca8119da11348d93ca302bbd125bde0db2b50edbe728a620bb9d3e6f706286aedea973425c0b9eedf8a38873544cf91badf49ad92a635a93f71ddfcee1eae536c25d1b270956be16588ef1cfef2f1d15f650bd5",
           "derive_key": "81720f34452f58a0120a58b6b4608384b5c51d11f39ce97161a0c0e442ca022550e7cd651e312f0b4c6afb3c348ae5dd17d2b29fab3b894d9a0034c7b04fd9190cbd90043ff65d1657bbc05bfdecf2897dd894c7a1b54656d59a50b51190a9da44db426266ad6ce7c173a8c0bbe091b75e734b4dadb59b2861cd2518b4e7591e4b83c9"
         },
         {
           "input_len": 129,
           "hash": "683aaae9f3c5ba37eaaf072aed0f9e30bac0865137bae68b1fde4ca2aebdcb12f96ffa7b36dd78ba321be7e842d364a62a42e3746681c8bace18a4a8a79649285c7127bf8febf125be9de39586d251f0d41da20980b70d35e3dac0eee59e468a894fa7e6a07129aaad09855f6ad4801512a116ba2b7841e6cfc99ad77594a8f2d181a7",
           "keyed_hash": "d4a64dae6cdccbac1e5287f54f17c5f985105457c1a2ec1878ebd4b57e20d38f1c9db018541eec241b748f87725665b7b1ace3e0065b29c3bcb232c90e37897fa5aaee7e1e8a2ecfcd9b51463e42238cfdd7fee1aecb3267fa7f2128079176132a412cd8aaf0791276f6b98ff67359bd8652ef3a203976d5ff1cd41885573487bcd683",
           "derive_key": "938d2d4435be30eafdbb2b7031f7857c98b04881227391dc40db3c7b21f41fc18d72d0f9c1de5760e1941aebf3100b51d64644cb459eb5d20258e233892805eb98b07570ef2a1787cd48e117c8d6a63a68fd8fc8e59e79dbe63129e88352865721c8d5f0cf183f85e0609860472b0d6087cefdd186d984b21542c1c780684ed6832d8d"
         },
         {
           "input_len": 1023,
           "hash": "10108970eeda3eb932baac1428c7a2163b0e924c9a9e25b35bba72b28f70bd11a182d27a591b05592b15607500e1e8dd56bc6c7fc063715b7a1d737df5bad3339c56778957d870eb9717b57ea3d9fb68d1b55127bba6a906a4a24bbd5acb2d123a37b28f9e9a81bbaae360d58f85e5fc9d75f7c370a0cc09b6522d9c8d822f2f28f485",
           "keyed_hash": "c951ecdf03288d0fcc96ee3413563d8a6d3589547f2c2fb36d9786470f1b9d6e890316d2e6d8b8c25b0a5b2180f94fb1a158ef508c3cde45e2966bd796a696d3e13efd86259d756387d9becf5c8bf1ce2192b87025152907b6d8cc33d17826d8b7b9bc97e38c3c85108ef09f013e01c229c20a83d9e8efac5b37470da28575fd755a10",
           "derive_key": "74a16c1c3d44368a86e1ca6df64be6a2f64cce8f09220787450722d85725dea59c413264404661e9e4d955409dfe4ad3aa487871bcd454ed12abfe2c2b1eb7757588cf6cb18d2eccad49e018c0d0fec323bec82bf1644c6325717d13ea712e6840d3e6e730d35553f59eff5377a9c350bcc1556694b924b858f329c44ee64b884ef00d"
         },
         {
           "input_len": 1024,
           "hash": "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af71cf8107265ecdaf8505b95d8fcec83a98a6a96ea5109d2c179c47a387ffbb404756f6eeae7883b446b70ebb144527c2075ab8ab204c0086bb22b7c93d465efc57f8d917f0b385c6df265e77003b85102967486ed57db5c5ca170ba441427ed9afa684e",
           "keyed_hash": "75c46f6f3d9eb4f55ecaaee480db732e6c2105546f1e675003687c31719c7ba4a78bc838c72852d4f49c864acb7adafe2478e824afe51c8919d06168414c265f298a8094b1ad813a9b8614acabac321f24ce61c5a5346eb519520d38ecc43e89b5000236df0597243e4d2493fd626730e2ba17ac4d8824d09d1a4a8f57b8227778e2de",
           "derive_key": "7356cd7720d5b66b6d0697eb3177d9f8d73a4a5c5e968896eb6a6896843027066c23b601d3ddfb391e90d5c8eccdef4ae2a264bce9e612ba15e2bc9d654af1481b2e75dbabe615974f1070bba84d56853265a34330b4766f8e75edd1f4a1650476c10802f22b64bd3919d246ba20a17558bc51c199efdec67e80a227251808d8ce5bad"
         },
         {
           "input_len": 1025,
           "hash": "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444f4c4a22b4b399155358a994e52bf255de60035742ec71bd08ac275a1b51cc6bfe332b0ef84b409108cda080e6269ed4b3e2c3f7d722aa4cdc98d16deb554e5627be8f955c98e1d5f9565a9194cad0c4285f93700062d9595adb992ae68ff12800ab67a",
           "keyed_hash": "357dc55de0c7e382c900fd6e320acc04146be01db6a8ce7210b7189bd664ea69362396b77fdc0d2634a552970843722066c3c15902ae5097e00ff53f1e116f1cd5352720113a837ab2452cafbde4d54085d9cf5d21ca613071551b25d52e69d6c81123872b6f19cd3bc1333edf0c52b94de23ba772cf82636cff4542540a7738d5b930",
           "derive_key": "effaa245f065fbf82ac186839a249707c3bddf6d3fdda22d1b95a3c970379bcb5d31013a167509e9066273ab6e2123bc835b408b067d88f96addb550d96b6852dad38e320b9d940f86db74d398c770f462118b35d2724efa13da97194491d96dd37c3c09cbef665953f2ee85ec83d88b88d11547a6f911c8217cca46defa2751e7f3ad"
         },
         {
           "input_len": 2048,
           "hash": "e776b6028c7cd22a4d0ba182a8bf62205d2ef576467e838ed6f2529b85fba24a9a60bf80001410ec9eea6698cd537939fad4749edd484cb541aced55cd9bf54764d063f23f6f1e32e12958ba5cfeb1bf618ad094266d4fc3c968c2088f677454c288c67ba0dba337b9d91c7e1ba586dc9a5bc2d5e90c14f53a8863ac75655461cea8f9",
           "keyed_hash": "879cf1fa2ea0e79126cb1063617a05b6ad9d0b696d0d757cf053439f60a99dd10173b961cd574288194b23ece278c330fbb8585485e74967f31352a8183aa782b2b22f26cdcadb61eed1a5bc144b8198fbb0c13abbf8e3192c145d0a5c21633b0ef86054f42809df823389ee40811a5910dcbd1018af31c3b43aa55201ed4edaac74fe",
           "derive_key": "7b2945cb4fef70885cc5d78a87bf6f6207dd901ff239201351ffac04e1088a23e2c11a1ebffcea4d80447867b61badb1383d842d4e79645d48dd82ccba290769caa7af8eaa1bd78a2a5e6e94fbdab78d9c7b74e894879f6a515257ccf6f95056f4e25390f24f6b35ffbb74b766202569b1d797f2d4bd9d17524c720107f985f4ddc583"
         },
         {
           "input_len": 2049,
           "hash": "5f4d72f40d7a5f82b15ca2b2e44b1de3c2ef86c426c95c1af0b687952256303096de31d71d74103403822a2e0bc1eb193e7aecc9643a76b7bbc0c9f9c52e8783aae98764ca468962b5c2ec92f0c74eb5448d519713e09413719431c802f948dd5d90425a4ecdadece9eb178d80f26efccae630734dff63340285adec2aed3b51073ad3",
           "keyed_hash": "9f29700902f7c86e514ddc4df1e3049f258b2472b6dd5267f61bf13983b78dd5f9a88abfefdfa1e00b418971f2b39c64ca621e8eb37fceac57fd0c8fc8e117d43b81447be22d5d8186f8f5919ba6bcc6846bd7d50726c06d245672c2ad4f61702c646499ee1173daa061ffe15bf45a631e2946d616a4c345822f1151284712f76b2b0e",
           "derive_key": "2ea477c5515cc3dd606512ee72bb3e0e758cfae7232826f35fb98ca1bcbdf27316d8e9e79081a80b046b60f6a263616f33ca464bd78d79fa18200d06c7fc9bffd808cc4755277a7d5e09da0f29ed150f6537ea9bed946227ff184cc66a72a5f8c1e4bd8b04e81cf40fe6dc4427ad5678311a61f4ffc39d195589bdbc670f63ae70f4b6"
         },
         {
           "input_len": 3072,
           "hash": "b98cb0ff3623be03326b373de6b9095218513e64f1ee2edd2525c7ad1e5cffd29a3f6b0b978d6608335c09dc94ccf682f9951cdfc501bfe47b9c9189a6fc7b404d120258506341a6d802857322fbd20d3e5dae05b95c88793fa83db1cb08e7d8008d1599b6209d78336e24839724c191b2a52a80448306e0daa84a3fdb566661a37e11",
           "keyed_hash": "044a0e7b172a312dc02a4c9a818c036ffa2776368d7f528268d2e6b5df19177022f302d0529e4174cc507c463671217975e81dab02b8fdeb0d7ccc7568dd22574c783a76be215441b32e91b9a904be8ea81f7a0afd14bad8ee7c8efc305ace5d3dd61b996febe8da4f56ca0919359a7533216e2999fc87ff7d8f176fbecb3d6f34278b",
           "derive_key": "050df97f8c2ead654d9bb3ab8c9178edcd902a32f8495949feadcc1e0480c46b3604131bbd6e3ba573b6dd682fa0a63e5b165d39fc43a625d00207607a2bfeb65ff1d29292152e26b298868e3b87be95d6458f6f2ce6118437b632415abe6ad522874bcd79e4030a5e7bad2efa90a7a7c67e93f0a18fb28369d0a9329ab5c24134ccb0"
         },
         {
           "input_len": 3073,
           "hash": "7124b49501012f81cc7f11ca069ec9226cecb8a2c850cfe644e327d22d3e1cd39a27ae3b79d68d89da9bf25bc27139ae65a324918a5f9b7828181e52cf373c84f35b639b7fccbb985b6f2fa56aea0c18f531203497b8bbd3a07ceb5926f1cab74d14bd66486d9a91eba99059a98bd1cd25876b2af5a76c3e9eed554ed72ea952b603bf",
           "keyed_hash": "68dede9bef00ba89e43f31a6825f4cf433389fedae75c04ee9f0cf16a427c95a96d6da3fe985054d3478865be9a092250839a697bbda74e279e8a9e69f0025e4cfddd6cfb434b1cd9543aaf97c635d1b451a4386041e4bb100f5e45407cbbc24fa53ea2de3536ccb329e4eb9466ec37093a42cf62b82903c696a93a50b702c80f3c3c5",
           "derive_key": "72613c9ec9ff7e40f8f5c173784c532ad852e827dba2bf85b2ab4b76f7079081576288e552647a9d86481c2cae75c2dd4e7c5195fb9ada1ef50e9c5098c249d743929191441301c69e1f48505a4305ec1778450ee48b8e69dc23a25960fe33070ea549119599760a8a2d28aeca06b8c5e9ba58bc19e11fe57b6ee98aa44b2a8e6b14a5"
         },
         {
           "input_len": 4096,
           "hash": "015094013f57a5277b59d8475c0501042c0b642e531b0a1c8f58d2163229e9690289e9409ddb1b99768eafe1623da896faf7e1114bebeadc1be30829b6f8af707d85c298f4f0ff4d9438aef948335612ae921e76d411c3a9111df62d27eaf871959ae0062b5492a0feb98ef3ed4af277f5395172dbe5c311918ea0074ce0036454f620",
           "keyed_hash": "befc660aea2f1718884cd8deb9902811d332f4fc4a38cf7c7300d597a081bfc0bbb64a36edb564e01e4b4aaf3b060092a6b838bea44afebd2deb8298fa562b7b597c757b9df4c911c3ca462e2ac89e9a787357aaf74c3b56d5c07bc93ce899568a3eb17d9250c20f6c5f6c1e792ec9a2dcb715398d5a6ec6d5c54f586a00403a1af1de",
           "derive_key": "1e0d7f3db8c414c97c6307cbda6cd27ac3b030949da8e23be1a1a924ad2f25b9d78038f7b198596c6cc4a9ccf93223c08722d684f240ff6569075ed81591fd93f9fff1110b3a75bc67e426012e5588959cc5a4c192173a03c00731cf84544f65a2fb9378989f72e9694a6a394a8a30997c2e67f95a504e631cd2c5f55246024761b245"
         },
         {
           "input_len": 4097,
           "hash": "9b4052b38f1c5fc8b1f9ff7ac7b27cd242487b3d890d15c96a1c25b8aa0fb99505f91b0b5600a11251652eacfa9497b31cd3c409ce2e45cfe6c0a016967316c426bd26f619eab5d70af9a418b845c608840390f361630bd497b1ab44019316357c61dbe091ce72fc16dc340ac3d6e009e050b3adac4b5b2c92e722cffdc46501531956",
           "keyed_hash": "00df940cd36bb9fa7cbbc3556744e0dbc8191401afe70520ba292ee3ca80abbc606db4976cfdd266ae0abf667d9481831ff12e0caa268e7d3e57260c0824115a54ce595ccc897786d9dcbf495599cfd90157186a46ec800a6763f1c59e36197e9939e900809f7077c102f888caaf864b253bc41eea812656d46742e4ea42769f89b83f",
           "derive_key": "aca51029626b55fda7117b42a7c211f8c6e9ba4fe5b7a8ca922f34299500ead8a897f66a400fed9198fd61dd2d58d382458e64e100128075fc54b860934e8de2e84170734b06e1d212a117100820dbc48292d148afa50567b8b84b1ec336ae10d40c8c975a624996e12de31abbe135d9d159375739c333798a80c64ae895e51e22f3ad"
         },
         {
           "input_len": 5120,
           "hash": "9cadc15fed8b5d854562b26a9536d9707cadeda9b143978f319ab34230535833acc61c8fdc114a2010ce8038c853e121e1544985133fccdd0a2d507e8e615e611e9a0ba4f47915f49e53d721816a9198e8b30f12d20ec3689989175f1bf7a300eee0d9321fad8da232ece6efb8e9fd81b42ad161f6b9550a069e66b11b40487a5f5059",
           "keyed_hash": "2c493e48e9b9bf31e0553a22b23503c0a3388f035cece68eb438d22fa1943e209b4dc9209cd80ce7c1f7c9a744658e7e288465717ae6e56d5463d4f80cdb2ef56495f6a4f5487f69749af0c34c2cdfa857f3056bf8d807336a14d7b89bf62bef2fb54f9af6a546f818dc1e98b9e07f8a5834da50fa28fb5874af91bf06020d1bf0120e",
           "derive_key": "7a7acac8a02adcf3038d74cdd1d34527de8a0fcc0ee3399d1262397ce5817f6055d0cefd84d9d57fe792d65a278fd20384ac6c30fdb340092f1a74a92ace99c482b28f0fc0ef3b923e56ade20c6dba47e49227166251337d80a037e987ad3a7f728b5ab6dfafd6e2ab1bd583a95d9c895ba9c2422c24ea0f62961f0dca45cad47bfa0d"
         },
         {
           "input_len": 5121,
           "hash": "628bd2cb2004694adaab7bbd778a25df25c47b9d4155a55f8fbd79f2fe154cff96adaab0613a6146cdaabe498c3a94e529d3fc1da2bd08edf54ed64d40dcd6777647eac51d8277d70219a9694334a68bc8f0f23e20b0ff70ada6f844542dfa32cd4204ca1846ef76d811cdb296f65e260227f477aa7aa008bac878f72257484f2b6c95",
           "keyed_hash": "6ccf1c34753e7a044db80798ecd0782a8f76f33563accaddbfbb2e0ea4b2d0240d07e63f13667a8d1490e5e04f13eb617aea16a8c8a5aaed1ef6fbde1b0515e3c81050b361af6ead126032998290b563e3caddeaebfab592e155f2e161fb7cba939092133f23f9e65245e58ec23457b78a2e8a125588aad6e07d7f11a85b88d375b72d",
           "derive_key": "b07f01e518e702f7ccb44a267e9e112d403a7b3f4883a47ffbed4b48339b3c341a0add0ac032ab5aaea1e4e5b004707ec5681ae0fcbe3796974c0b1cf31a194740c14519273eedaabec832e8a784b6e7cfc2c5952677e6c3f2c3914454082d7eb1ce1766ac7d75a4d3001fc89544dd46b5147382240d689bbbaefc359fb6ae30263165"
         },
         {
           "input_len": 6144,
           "hash": "3e2e5b74e048f3add6d21faab3f83aa44d3b2278afb83b80b3c35164ebeca2054d742022da6fdda444ebc384b04a54c3ac5839b49da7d39f6d8a9db03deab32aade156c1c0311e9b3435cde0ddba0dce7b26a376cad121294b689193508dd63151603c6ddb866ad16c2ee41585d1633a2cea093bea714f4c5d6b903522045b20395c83",
           "keyed_hash": "3d6b6d21281d0ade5b2b016ae4034c5dec10ca7e475f90f76eac7138e9bc8f1dc35754060091dc5caf3efabe0603c60f45e415bb3407db67e6beb3d11cf8e4f7907561f05dace0c15807f4b5f389c841eb114d81a82c02a00b57206b1d11fa6e803486b048a5ce87105a686dee041207e095323dfe172df73deb8c9532066d88f9da7e",
           "derive_key": "2a95beae63ddce523762355cf4b9c1d8f131465780a391286a5d01abb5683a1597099e3c6488aab6c48f3c15dbe1942d21dbcdc12115d19a8b8465fb54e9053323a9178e4275647f1a9927f6439e52b7031a0b465c861a3fc531527f7758b2b888cf2f20582e9e2c593709c0a44f9c6e0f8b963994882ea4168827823eef1f64169fef"
         },
         {
           "input_len": 6145,
           "hash": "f1323a8631446cc50536a9f705ee5cb619424d46887f3c376c695b70e0f0507f18a2cfdd73c6e39dd75ce7c1c6e3ef238fd54465f053b25d21044ccb2093beb015015532b108313b5829c3621ce324b8e14229091b7c93f32db2e4e63126a377d2a63a3597997d4f1cba59309cb4af240ba70cebff9a23d5e3ff0cdae2cfd54e070022",
           "keyed_hash": "9ac301e9e39e45e3250a7e3b3df701aa0fb6889fbd80eeecf28dbc6300fbc539f3c184ca2f59780e27a576c1d1fb9772e99fd17881d02ac7dfd39675aca918453283ed8c3169085ef4a466b91c1649cc341dfdee60e32231fc34c9c4e0b9a2ba87ca8f372589c744c15fd6f985eec15e98136f25beeb4b13c4e43dc84abcc79cd4646c",
           "derive_key": "379bcc61d0051dd489f686c13de00d5b14c505245103dc040d9e4dd1facab8e5114493d029bdbd295aaa744a59e31f35c7f52dba9c3642f773dd0b4262a9980a2aef811697e1305d37ba9d8b6d850ef07fe41108993180cf779aeece363704c76483458603bbeeb693cffbbe5588d1f3535dcad888893e53d977424bb707201569a8d2"
         },
         {
           "input_len": 7168,
           "hash": "61da957ec2499a95d6b8023e2b0e604ec7f6b50e80a9678b89d2628e99ada77a5707c321c83361793b9af62a40f43b523df1c8633cecb4cd14d00bdc79c78fca5165b863893f6d38b02ff7236c5a9a8ad2dba87d24c547cab046c29fc5bc1ed142e1de4763613bb162a5a538e6ef05ed05199d751f9eb58d332791b8d73fb74e4fce95",
           "keyed_hash": "b42835e40e9d4a7f42ad8cc04f85a963a76e18198377ed84adddeaecacc6f3fca2f01d5277d69bb681c70fa8d36094f73ec06e452c80d2ff2257ed82e7ba348400989a65ee8daa7094ae0933e3d2210ac6395c4af24f91c2b590ef87d7788d7066ea3eaebca4c08a4f14b9a27644f99084c3543711b64a070b94f2c9d1d8a90d035d52",
           "derive_key": "11c37a112765370c94a51415d0d651190c288566e295d505defdad895dae223730d5a5175a38841693020669c7638f40b9bc1f9f39cf98bda7a5b54ae24218a800a2116b34665aa95d846d97ea988bfcb53dd9c055d588fa21ba78996776ea6c40bc428b53c62b5f3ccf200f647a5aae8067f0ea1976391fcc72af1945100e2a6dcb88"
         },
         {
           "input_len": 7169,
           "hash": "a003fc7a51754a9b3c7fae0367ab3d782dccf28855a03d435f8cfe74605e781798a8b20534be1ca9eb2ae2df3fae2ea60e48c6fb0b850b1385b5de0fe460dbe9d9f9b0d8db4435da75c601156df9d047f4ede008732eb17adc05d96180f8a73548522840779e6062d643b79478a6e8dbce68927f36ebf676ffa7d72d5f68f050b119c8",
           "keyed_hash": "ed9b1a922c046fdb3d423ae34e143b05ca1bf28b710432857bf738bcedbfa5113c9e28d72fcbfc020814ce3f5d4fc867f01c8f5b6caf305b3ea8a8ba2da3ab69fabcb438f19ff11f5378ad4484d75c478de425fb8e6ee809b54eec9bdb184315dc856617c09f5340451bf42fd3270a7b0b6566169f242e533777604c118a6358250f54",
           "derive_key": "554b0a5efea9ef183f2f9b931b7497995d9eb26f5c5c6dad2b97d62fc5ac31d99b20652c016d88ba2a611bbd761668d5eda3e568e940faae24b0d9991c3bd25a65f770b89fdcadabcb3d1a9c1cb63e69721cacf1ae69fefdcef1e3ef41bc5312ccc17222199e47a26552c6adc460cf47a72319cb5039369d0060eaea59d6c65130f1dd"
         },
         {
           "input_len": 8192,
           "hash": "aae792484c8efe4f19e2ca7d371d8c467ffb10748d8a5a1ae579948f718a2a635fe51a27db045a567c1ad51be5aa34c01c6651c4d9b5b5ac5d0fd58cf18dd61a47778566b797a8c67df7b1d60b97b19288d2d877bb2df417ace009dcb0241ca1257d62712b6a4043b4ff33f690d849da91ea3bf711ed583cb7b7a7da2839ba71309bbf",
           "keyed_hash": "dc9637c8845a770b4cbf76b8daec0eebf7dc2eac11498517f08d44c8fc00d58a4834464159dcbc12a0ba0c6d6eb41bac0ed6585cabfe0aca36a375e6c5480c22afdc40785c170f5a6b8a1107dbee282318d00d915ac9ed1143ad40765ec120042ee121cd2baa36250c618adaf9e27260fda2f94dea8fb6f08c04f8f10c78292aa46102",
           "derive_key": "ad01d7ae4ad059b0d33baa3c01319dcf8088094d0359e5fd45d6aeaa8b2d0c3d4c9e58958553513b67f84f8eac653aeeb02ae1d5672dcecf91cd9985a0e67f4501910ecba25555395427ccc7241d70dc21c190e2aadee875e5aae6bf1912837e53411dabf7a56cbf8e4fb780432b0d7fe6cec45024a0788cf5874616407757e9e6bef7"
         },
         {
           "input_len": 8193,
           "hash": "bab6c09cb8ce8cf459261398d2e7aef35700bf488116ceb94a36d0f5f1b7bc3bb2282aa69be089359ea1154b9a9286c4a56af4de975a9aa4a5c497654914d279bea60bb6d2cf7225a2fa0ff5ef56bbe4b149f3ed15860f78b4e2ad04e158e375c1e0c0b551cd7dfc82f1b155c11b6b3ed51ec9edb30d133653bb5709d1dbd55f4e1ff6",
           "keyed_hash": "954a2a75420c8d6547e3ba5b98d963e6fa6491addc8c023189cc519821b4a1f5f03228648fd983aef045c2fa8290934b0866b615f585149587dda2299039965328835a2b18f1d63b7e300fc76ff260b571839fe44876a4eae66cbac8c67694411ed7e09df51068a22c6e67d6d3dd2cca8ff12e3275384006c80f4db68023f24eebba57",
           "derive_key": "af1e0346e389b17c23200270a64aa4e1ead98c61695d917de7d5b00491c9b0f12f20a01d6d622edf3de026a4db4e4526225debb93c1237934d71c7340bb5916158cbdafe9ac3225476b6ab57a12357db3abbad7a26c6e66290e44034fb08a20a8d0ec264f309994d2810c49cfba6989d7abb095897459f5425adb48aba07c5fb3c83c0"
         },
         {
           "input_len": 16384,
           "hash": "f875d6646de28985646f34ee13be9a576fd515f76b5b0a26bb324735041ddde49d764c270176e53e97bdffa58d549073f2c660be0e81293767ed4e4929f9ad34bbb39a529334c57c4a381ffd2a6d4bfdbf1482651b172aa883cc13408fa67758a3e47503f93f87720a3177325f7823251b85275f64636a8f1d599c2e49722f42e93893",
           "keyed_hash": "9e9fc4eb7cf081ea7c47d1807790ed211bfec56aa25bb7037784c13c4b707b0df9e601b101e4cf63a404dfe50f2e1865bb12edc8fca166579ce0c70dba5a5c0fc960ad6f3772183416a00bd29d4c6e651ea7620bb100c9449858bf14e1ddc9ecd35725581ca5b9160de04060045993d972571c3e8f71e9d0496bfa744656861b169d65",
           "derive_key": "160e18b5878cd0df1c3af85eb25a0db5344d43a6fbd7a8ef4ed98d0714c3f7e160dc0b1f09caa35f2f417b9ef309dfe5ebd67f4c9507995a531374d099cf8ae317542e885ec6f589378864d3ea98716b3bbb65ef4ab5e0ab5bb298a501f19a41ec19af84a5e6b428ecd813b1a47ed91c9657c3fba11c406bc316768b58f6802c9e9b57"
         },
         {
           "input_len": 31744,
           "hash": "62b6960e1a44bcc1eb1a611a8d6235b6b4b78f32e7abc4fb4c6cdcce94895c47860cc51f2b0c28a7b77304bd55fe73af663c02d3f52ea053ba43431ca5bab7bfea2f5e9d7121770d88f70ae9649ea713087d1914f7f312147e247f87eb2d4ffef0ac978bf7b6579d57d533355aa20b8b77b13fd09748728a5cc327a8ec470f4013226f",
           "keyed_hash": "efa53b389ab67c593dba624d898d0f7353ab99e4ac9d42302ee64cbf9939a4193a7258db2d9cd32a7a3ecfce46144114b15c2fcb68a618a976bd74515d47be08b628be420b5e830fade7c080e351a076fbc38641ad80c736c8a18fe3c66ce12f95c61c2462a9770d60d0f77115bbcd3782b593016a4e728d4c06cee4505cb0c08a42ec",
           "derive_key": "39772aef80e0ebe60596361e45b061e8f417429d529171b6764468c22928e28e9759adeb797a3fbf771b1bcea30150a020e317982bf0d6e7d14dd9f064bc11025c25f31e81bd78a921db0174f03dd481d30e93fd8e90f8b2fee209f849f2d2a52f31719a490fb0ba7aea1e09814ee912eba111a9fde9d5c274185f7bae8ba85d300a2b"
         },
         {
           "input_len": 102400,
           "hash": "bc3e3d41a1146b069abffad3c0d44860cf664390afce4d9661f7902e7943e085e01c59dab908c04c3342b816941a26d69c2605ebee5ec5291cc55e15b76146e6745f0601156c3596cb75065a9c57f35585a52e1ac70f69131c23d611ce11ee4ab1ec2c009012d236648e77be9295dd0426f29b764d65de58eb7d01dd42248204f45f8e",
           "keyed_hash": "1c35d1a5811083fd7119f5d5d1ba027b4d01c0c6c49fb6ff2cf75393ea5db4a7f9dbdd3e1d81dcbca3ba241bb18760f207710b751846faaeb9dff8262710999a59b2aa1aca298a032d94eacfadf1aa192418eb54808db23b56e34213266aa08499a16b354f018fc4967d05f8b9d2ad87a7278337be9693fc638a3bfdbe314574ee6fc4",
           "derive_key": "4652cff7a3f385a6103b5c260fc1593e13c778dbe608efb092fe7ee69df6e9c6d83a3e041bc3a48df2879f4a0a3ed40e7c961c73eff740f3117a0504c2dff4786d44fb17f1549eb0ba585e40ec29bf7732f0b7e286ff8acddc4cb1e23b87ff5d824a986458dcc6a04ac83969b80637562953df51ed1a7e90a7926924d2763778be8560"
         }
      ]]
      local key = "whats the Elvish word for friend"
      local context_string = "BLAKE3 2019-12-27 16:29:52 test vectors context"
      local input = ("\0"..("."):rep(250):gsub("().", string.char)):rep(math.ceil(102400 / 251))
      local cnt = 0
      for vec in test_vectors:gmatch'%b{}' do
         local input_len, hash, keyed_hash, derive_key = assert(vec:match'"input_len": (%d+),%s*"hash": "(%x+)",%s*"keyed_hash": "(%x+)",%s*"derive_key": "(%x+)"')
         local input = input:sub(1, tonumber(input_len))
         assert(hash       == sha.blake3(input, nil, #hash / 2))
         assert(keyed_hash == sha.blake3(input, key, #keyed_hash / 2))
         assert(derive_key == sha.blake3_derive_key(input, context_string, #derive_key / 2))
         cnt = cnt + 1
      end
      assert(cnt == 35)
   end

   assert(sha.blake3("") == "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262")
   assert(sha.blake3("message")           == "4bd766dabadb76f246b13b877e09eeca2c5e74a55d3e6828cbaf9edcaa4e055a")
   assert(sha.blake3("message", nil, 132) == "4bd766dabadb76f246b13b877e09eeca2c5e74a55d3e6828cbaf9edcaa4e055aa2f85cc9d1ca73cf2ed0991c14f76e176b7625d5e0df216ee3222954fb2164210ebb392bbe596b9b111dc8fc65b09f18f64c2d2eb9b1753694564a933bc8f169434742c2fd7c002d267d2ec1447d8a246dae450b58328e71e52e619873e988713e261bbc")
   assert(sha.blake3("message", "salt")      == "0b28ff073e5c22c352515466304d53ab6c5aa605af0cb9a7fcd47bf881d0f800")
   assert(sha.blake3("message", "salt", 132) == "0b28ff073e5c22c352515466304d53ab6c5aa605af0cb9a7fcd47bf881d0f80091d7d71b85811f81bd85ad58f85ece83a20faf0a134aa96a8354c7debe90526eb194453ce52a03cdd349923a8816d57eedfcfa95a7871c7e2b5b0ad2b9061ddf809f83ccd08d8cdd4dc579ed38cb4ec8303886c2aa32ee34696d9b1a0373f94d62669585")
   assert(sha.blake3("message", "key")      == "d6c4acea3d08d217ffa77c4f821c866945165173c996ce997f808956185a776f")
   assert(sha.blake3("message", "key", 132) == "d6c4acea3d08d217ffa77c4f821c866945165173c996ce997f808956185a776fa261099f68a44266ed335362b6c12ad20b61800fe66fe7f0d74dd7c1ba777e60f229aaabe2300c8ac8856ab0c7f0f5df1a06fc2a7131257d729805334f032065d5a4934e86e51e080785cc63d192f57d53e45f192226bd24998ed99064a0b73ef003ab0b")
   assert(sha.blake3(("€"):rep(100)) == "20b089f9099e151d25649583b1dc1517c7cb29f7dcdad5e87daae10a41a3ff10")
   assert(sha.blake3(("€"):rep(100), "100 euro") == "5d3b88a45654617dc1aed27c3a230e42e9d4a15951572f542a005278e480c831")
   assert(sha.blake3(("\255"):rep(999), ("\255"):rep(32)) == "18f4ea688d82cbcd7ad4db10a14d9eea1cde44573b8111835de95b2ede26a652")

   do
      local context = "my unique personalization string"
      local master_key = "my master key"
      local derived_key = sha.hex_to_bin(sha.blake3_derive_key(master_key, context))
      assert(sha.blake3("my message", derived_key) == "707e579854238b4dc510048808b47e94327b1f3898613e24806a5b047d78d0ed")
   end

   do
      local function create_personalized_keyed_hash_function(key, personalization_string, digest_size_in_bytes)
         -- create personalized 256-bit key
         local derived_key = sha.hex_to_bin(sha.blake3_derive_key(key, personalization_string))
         return function (message)
            -- pass the personalized key to BLAKE3
            return sha.blake3(message, derived_key, digest_size_in_bytes)
         end
      end
      local password = "password"
      -- create two different 160-bit hash functions depending on common password
      local H1 = create_personalized_keyed_hash_function(password, "personalization string 1", 20)
      local H2 = create_personalized_keyed_hash_function(password, "personalization string 2", 20)
      -- usual BLAKE3 without personalization
      assert(sha.blake3("message", password, 20) == "aff235a529b0251acef680e643aabef619cb45bf")
      -- personalized BLAKE3
      assert(H1("message") == "b66b08dec065ef767baa56457e3591cfa9232554")
      assert(H2("message") == "12f6db5e20d6cb492ba6c56f5521343f345a0aeb")
   end

   assert(sha.blake3("The quick brown fox jumps over the lazy dog")          == "2f1514181aadccd913abd94cfa592701a5686ab23f8df1dff1b74710febc6d4a")
   assert(sha.blake3("The quick brown fox jumps over the lazy dog", nil, 70) == "2f1514181aadccd913abd94cfa592701a5686ab23f8df1dff1b74710febc6d4ac0615cd845be939b4ef6aec25e799aaa450c63f8d9e333cdb0dd79b70ee698793ca5d743d5be")
   local get_next_part_of_digest = sha.blake3("The quick brown fox jumps over the lazy dog", nil, -11)
   assert(get_next_part_of_digest(5) == "2f1514181a") -- 5 bytes in hexadecimal representation
   assert(get_next_part_of_digest()  == "ad")         -- size=1 is assumed when omitted
   assert(get_next_part_of_digest(0) == "")           -- size=0 is a valid size
   assert(get_next_part_of_digest(3) == "ccd913")     -- next 3 bytes
   assert(get_next_part_of_digest(3) == "abd9")       -- last 2 bytes (although 3 were requested)
   assert(get_next_part_of_digest(3) == "")           -- empty strings beyond the end of the digest
   get_next_part_of_digest("seek", 0)                 -- jump to the beginning
   assert(get_next_part_of_digest(7) == "2f1514181aadcc")
   assert(get_next_part_of_digest(7) == "d913abd9")
   assert(get_next_part_of_digest(7) == "")

   local append_input_message = sha.blake3(nil, nil, -1)  -- infinite digest, "chunk-by-chunk" input mode, "chunk-by-chunk" output mode
   append_input_message("The quick brown fox")
   append_input_message(" jumps over the lazy dog")
   local get_next_part_of_digest = append_input_message()  -- input stream is terminated, now we can start receiving the output stream
   assert(get_next_part_of_digest(10) == "2f1514181aadccd913ab")
   get_next_part_of_digest("seek", -5555)
   assert(get_next_part_of_digest(5555 + 10) == "2f1514181aadccd913ab")
   get_next_part_of_digest("seek", 2^31-10)
   assert(get_next_part_of_digest(20) == "a224c58b681656471bb49c5773c9f545cbd338e3")
   get_next_part_of_digest("seek", 2^32-10)
   assert(get_next_part_of_digest(20) == "85ae3f8181acb602df2a104ffc4b1faf9e5156d3")
   get_next_part_of_digest("seek", 64*2^31-10)
   assert(get_next_part_of_digest(20) == "473705d164998022de631a525db16245e363eb78")
   get_next_part_of_digest("seek", 64*2^32-10)
   assert(get_next_part_of_digest(20) == "ce1b8f63b57d26fd525debe3bdd15ac2a0aeb975")
   get_next_part_of_digest("seek", 2^53-10)
   assert(get_next_part_of_digest(20) == "db5aa1a73e9386ab0c05")
   get_next_part_of_digest("seek", 2^53)
   assert(get_next_part_of_digest(1) == "")

   -- useless special case: digest of length 0
   assert(sha.blake3("The quick brown fox jumps over the lazy dog", nil, 0) == "")
   local append_input_message = sha.blake3(nil, nil, 0)  -- "chunk-by-chunk" input mode
   append_input_message("The quick brown fox")
   append_input_message(" jumps over the lazy dog")
   assert(append_input_message() == "")

end


local function test_hmac()

   local hmac = sha.hmac

   assert(hmac(sha.sha1,   "your key", "your message") == "317d0dfd868a5c06c9444ac1328aa3e2bfd29fb2")
   assert(hmac(sha.sha512, "your key", "your message") == "2f5ddcdbd062a5392f07b0cd0262bf52c21bfb3db513296240cca8d5accc09d18d96be0a94995be4494c032f1eda946ad549fb61ccbe985d160f0b2f9588d34b")
   assert(hmac(sha.md5,    "", "") == "74e6f7298a9c2d168935f58c001bad88")
   assert(hmac(sha.sha256, "", "") == "b613679a0814d9ec772f95d778c35fc5ff1697c493715653c6c712144292c5ad")
   assert(hmac(sha.sha1,   "", "") == "fbdb1d1b18aa6c08324b7d64b71fb76370690e1d")
   assert(hmac(sha.md5,    "key", "The quick brown fox jumps over the lazy dog") == "80070713463e7749b90c2dc24911e275")
   assert(hmac(sha.sha256, "key", "The quick brown fox jumps over the lazy dog") == "f7bc83f430538424b13298e6aa6fb143ef4d59a14946175997479dbc2d1a3cd8")
   assert(hmac(sha.sha1,   "key", "The quick brown fox jumps over the lazy dog") == "de7c9b85b8b78aa6bc8a7a36f70a90701c9db4d9")

   -- chunk-by-chunk mode
   local append = hmac(sha.sha1, "key")
   append("The quick brown fox")
   append("")  -- empty string is allowed as a valid chunk
   append(" jumps over the lazy dog")
   assert(append() == "de7c9b85b8b78aa6bc8a7a36f70a90701c9db4d9")  -- invocation without an argument receives the result

   local key, message = ("\170"):rep(131), "Test Using Larger Than Block-Size Key - Hash Key First"
   assert(hmac(sha.sha3_224, key, message) == "b4a1f04c00287a9b7f6075b313d279b833bc8f75124352d05fb9995f")
   assert(hmac(sha.sha3_256, key, message) == "ed73a374b96c005235f948032f09674a58c0ce555cfc1f223b02356560312c3b")
   assert(hmac(sha.sha3_384, key, message) == "0fc19513bf6bd878037016706a0e57bc528139836b9a42c3d419e498e0e1fb9616fd669138d33a1105e07c72b6953bcc")
   assert(hmac(sha.sha3_512, key, message) == "00f751a9e50695b090ed6911a4b65524951cdc15a73a5d58bb55215ea2cd839ac79d2b44a39bafab27e83fde9e11f6340b11d991b1b91bf2eee7fc872426c3a4")

   assert(not pcall(hmac, function(x) return sha.sha256(x) end, "key", "message"))  -- must raise "unknown hash function" error

end


local function test_base64()

   local bin_to_base64 = sha.bin2base64
   assert(bin_to_base64""       == ""        )
   assert(bin_to_base64"f"      == "Zg=="    )
   assert(bin_to_base64"fo"     == "Zm8="    )
   assert(bin_to_base64"foo"    == "Zm9v"    )
   assert(bin_to_base64"foob"   == "Zm9vYg==")
   assert(bin_to_base64"fooba"  == "Zm9vYmE=")
   assert(bin_to_base64"foobar" == "Zm9vYmFy")

   local base64_to_bin = sha.base642bin
   assert(base64_to_bin""         == ""      )
   assert(base64_to_bin"Zg=="     == "f"     )
   assert(base64_to_bin"Zm8="     == "fo"    )
   assert(base64_to_bin"Zm9v"     == "foo"   )
   assert(base64_to_bin"Zm9vYg==" == "foob"  )
   assert(base64_to_bin"Zm9vYmE=" == "fooba" )
   assert(base64_to_bin"Zm9vYmFy" == "foobar")

   assert(sha.hex_to_bin"000961ff" == "\0\ta\255")
   assert(sha.bin_to_hex"\0\ta\255" == "000961ff")

end



local function test_all()

   test_md5()

   test_sha1()

   test_sha256()

   assert(sha.sha224"abc" == "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7")
   assert(sha.sha224"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" == "75388b16512776cc5dba5da1fd890150b0c6455cb4f58b1952522525")

   test_sha512()

   assert(sha.sha384"abc" == "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7")
   assert(sha.sha384"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu" == "09330c33f71147e83d192fc782cd1b4753111b173b3b05d22fa08086e3b0f712fcc7c71a557e2db966c3e9fa91746039")

   assert(sha.sha512_224"abc" == "4634270f707b6a54daae7530460842e20e37ed265ceee9a43e8924aa")
   assert(sha.sha512_224"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu" == "23fec5bb94d60b23308192640b0c453335d664734fe40e7268674af9")

   assert(sha.sha512_256"abc" == "53048e2681941ef99b2e29b76b4c7dabe4c2d0c634fc6d46e0e2f13107e7af23")
   assert(sha.sha512_256"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu" == "3928e184fb8690f840da3988121d31be65cb9d3ef83ee6146feac861e19b563a")

   test_sha3()

   test_blake2()

   test_blake3()

   test_hmac()

   test_base64()

   print"All tests passed"

end


test_all()

