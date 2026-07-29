local function returns_many()
    return 1, 2, 3, 4, 5
end

local function returns_copy()
    return returns_many()
end

print(returns_many())
print(returns_copy())

local a, b, c = returns_many()
print(a, b, c)

local d, e, f, g, h, i = returns_many()
print(d, e, f, g, h, i)
