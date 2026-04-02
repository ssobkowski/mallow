local function returns_many()
    return "A", "B", "C"
end

local packed = { returns_many() }
for i, value in ipairs(packed) do
    print("packed", i, value)
end

local mixed = { 0, returns_many() }
for i, value in ipairs(mixed) do
    print("mixed", i, value)
end

local doubled = { returns_many(), returns_many() }
for i, value in ipairs(doubled) do
    print("doubled", i, value)
end

local target = {}
target[1] = returns_many()
target[2] = (returns_many())
print(target[1], target[2])
