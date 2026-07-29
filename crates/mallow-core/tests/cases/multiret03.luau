local function returns_many()
    return "X", "Y", "Z"
end

local function capture(...)
    print(select("#", ...), ...)
end

capture(returns_many())
capture("head", returns_many())
capture(returns_many(), returns_many())

local function pair()
    return returns_many(), "tail"
end

print(pair())

local ok, x, y, z = pcall(returns_many)
print(ok, x, y, z)
