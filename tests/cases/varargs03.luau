local function inner(...)
    return ...
end

local function outer(...)
    return inner(...)
end

local a, b, c = outer(7, 8, 9)
print(a)
print(b)
print(c)
