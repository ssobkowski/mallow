local function pair()
    return 1, "x"
end

local function take(a, b, c)
    return a, b, c
end

local a, b, c = true, pair()
local d, e = pair(), "tail"
local f, g = (pair())
local x, y, z = take(true, pair())
local values = { true, pair() }

local object = {}
function object:take(a, b)
    return a, b
end
local m, n = object:take(pair())

local function forward(...)
    return ...
end
local p, q = forward("s", 42)

local function packed()
    return { pair() }
end
local packed_values = packed()

print(a, b, c, d, e, f, g, x, y, z, values, object, m, n, p, q, packed, packed_values)
