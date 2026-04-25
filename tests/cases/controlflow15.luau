local x = 0
local y = 0

while x < 5 and y < 3 do
    x = x + 1
    if x % 2 == 0 then
        y = y + 1
    end
    print("and-loop", x, y)
end

print("after-and", x, y)

local a = 10
local b = 10

while a > 5 or b > 7 do
    a = a - 1
    b = b - 1
    print("or-loop", a, b)
end

print("after-or", a, b)

local i = 10
local j = 10
local k = 10

while i > 5 or j > 7 or k > 4 do
    i -= 1
    k -= 1
    j -= 1
    print("or-loop2", i, j, k)
end

print("after-or2", i, j, k)
