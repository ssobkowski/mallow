local t = {}
for i = 1, 5 do
    t[i] = i * 10
end
print(table.concat(t, ","))

t[3] = nil
print(#t)
for i = 1, 5 do
    if t[i] ~= nil then
        print(i, t[i])
    end
end

local hybrid = {1, 2, 3}
print(#hybrid)
hybrid.key = "value"
print(#hybrid)
print(hybrid[1])
print(hybrid.key)

local clear = {a = 1, b = 2, c = 3}
print(clear.a, clear.b, clear.c)
clear.a = nil
clear.b = nil
clear.c = nil
print(clear.a, clear.b, clear.c)

local overwrite = {x = "old"}
print(overwrite.x)
overwrite.x = "new"
print(overwrite.x)

local arr = {1, 2, 3}
arr[4] = 4
arr[5] = 5
arr[10] = 10
print(table.concat(arr, ",", 1, 3))
print(arr[4])
print(arr[10])

local mut = {a = 1, b = 2}
for k, v in pairs(mut) do
    print(k, v)
    if k == "a" then
        mut.c = 3
    end
end
