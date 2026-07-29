local results = {}
local function risky(i)
    if i == 3 then error("three is cursed") end
    return i * 2
end

for i = 1, 5 do
    local ok, val = pcall(risky, i)
    if ok then
        table.insert(results, val)
    else
        table.insert(results, -1)
    end
end

print(results[1])
print(results[2])
print(results[3])
print(results[4])
print(results[5])
