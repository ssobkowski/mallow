-- note: this testcase's O0 variant is broken on Luau 0.715 due to an upstream bug

local int = 9223372036854775805i
print(int, integer.create(3), typeof(int))

print(integer.add(3i, 4i))
