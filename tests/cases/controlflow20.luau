local x = 0
local y = 0

repeat
    x = x + 1
    if x % 3 == 0 then
        y = y + 1
    end
    print("and-loop", x, y)
until x >= 5 and y >= 2

print("after-and", x, y)

local a = 0
local b = 0

repeat
    a = a + 1
    if a % 2 == 0 then
        b = b + 1
    end
    print("or-loop", a, b)
until a >= 6 or b >= 3

print("after-or", a, b)
