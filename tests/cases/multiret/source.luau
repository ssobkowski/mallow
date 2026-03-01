local function returns_many()
    return 1, 2, 3, 4, 5
end
print(returns_many())

local a, b, c = returns_many()
print(a, b, c)
local d, e, f, g, h, i = returns_many()
print(d, e, f, g, h, i)

local t = { returns_many() }
for i, v in t do
    print(i, v)
end

local u = {}
u[1] = returns_many()

for i, v in u do
    print(i, v)
end

local v = { returns_many(), returns_many() }
for i, w in v do
    print(i, w)
end
