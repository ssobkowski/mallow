local sum = 0

for i = 1, 5 do
    sum = sum + i
end

local stepped = {}

for i = 2, 10, 2 do
    table.insert(stepped, i)
end

print(sum)
print(table.concat(stepped, ","))
