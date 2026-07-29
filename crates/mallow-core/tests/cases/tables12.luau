local mixed = {10, 20, 30, key = "value", another = "data"}

print("-- ipairs --")
for i, v in ipairs(mixed) do
    print(i, v)
end

print("-- pairs --")
for k, v in pairs(mixed) do
    print(k, v)
end

local empty = {}
print("-- empty pairs --")
for k, v in pairs(empty) do
    print(k, v)
end
print("-- empty ipairs --")
for i, v in ipairs(empty) do
    print(i, v)
end

local sparse = {[1] = "a", [3] = "c", [5] = "e"}
print("-- sparse ipairs --")
for i, v in ipairs(sparse) do
    print(i, v)
end
print("-- sparse pairs --")
for k, v in pairs(sparse) do
    print(k, v)
end

local hash = {z = 1, a = 2, m = 3}
local keys = {}
for k, v in pairs(hash) do
    table.insert(keys, k)
end
table.sort(keys)
for _, k in ipairs(keys) do
    print(k, hash[k])
end

local with_gap = {1, 2, 3, nil, 5}
print("-- with gap ipairs --")
for i, v in ipairs(with_gap) do
    print(i, v)
end
print("-- with gap pairs --")
for k, v in pairs(with_gap) do
    print(k, v)
end

local t = {a = 1, b = 2, c = 3}
print("-- using next directly --")
local k, v = next(t, nil)
while k ~= nil do
    print(k, v)
    k, v = next(t, k)
end

local outer = {
    {1, 2},
    {3, 4},
    {5, 6}
}
print("-- nested --")
for i, inner in ipairs(outer) do
    for j, val in ipairs(inner) do
        print(i, j, val)
    end
end

local boolkeys = {[true] = "yes", [false] = "no"}
for k, v in pairs(boolkeys) do
    print(k, v)
end
