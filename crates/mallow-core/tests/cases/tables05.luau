local sparse = {}
sparse[1] = "one"
sparse[5] = "five"
sparse[10] = "ten"
print(sparse[1])
print(sparse[5])
print(sparse[10])
print(#sparse)

local t = {}
t[1000] = "thousand"
t[10000] = "ten thousand"
print(t[1000])
print(t[10000])

local mixed = {}
mixed[1] = "first"
mixed[100] = "hundredth"
mixed.key = "value"
mixed[-5] = "negative"
print(mixed[1])
print(mixed[100])
print(mixed.key)
print(mixed[-5])

local hash_only = {
    a = 1,
    b = 2,
    c = 3
}
print(#hash_only)
print(hash_only.a)
print(hash_only.b)
print(hash_only.c)

local with_gaps = {1, 2, nil, 4, nil, 6}
print(#with_gaps)
for i = 1, 6 do
    if with_gaps[i] ~= nil then
        print(i, with_gaps[i])
    end
end
