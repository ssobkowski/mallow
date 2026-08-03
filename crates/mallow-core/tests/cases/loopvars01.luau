local function join(values)
    return table.concat(values, ",")
end

local generic_values = {}
for _, value in ipairs({ 1, 2, 3 }) do
    value *= 10
    table.insert(generic_values, value)
end

local generic_pairs = {}
for key, value in ipairs({ "a", "b", "c" }) do
    key += 10
    value = value .. tostring(key)
    generic_pairs[key] = value
end

local generic_branch = {}
for _, value in ipairs({ 1, 2, 3, 4 }) do
    if value % 2 == 0 then
        value += 100
    else
        value -= 1
    end
    table.insert(generic_branch, value)
end

local generic_map = {}
for key, value in pairs({ left = 1, right = 2 }) do
    key = key .. "!"
    value += 10
    generic_map[key] = value
end

local numeric_values = {}
for i = 1, 4 do
    i *= 2
    table.insert(numeric_values, i)
end

local numeric_assignment = {}
for i = 1, 3 do
    i = i * 3
    table.insert(numeric_assignment, i)
end

local numeric_branch = {}
for i = 1, 4 do
    if i % 2 == 0 then
        i += 10
    else
        i -= 1
    end
    table.insert(numeric_branch, i)
end

local numeric_nested = {}
for i = 1, 3 do
    i += 10
    for j = 1, 2 do
        j += i
        table.insert(numeric_nested, i * 100 + j)
    end
end

assert(join(generic_values) == "10,20,30")
assert(generic_pairs[11] == "a11")
assert(generic_pairs[12] == "b12")
assert(generic_pairs[13] == "c13")
assert(join(generic_branch) == "0,102,2,104")
assert(generic_map["left!"] == 11)
assert(generic_map["right!"] == 12)
assert(join(numeric_values) == "2,4,6,8")
assert(join(numeric_assignment) == "3,6,9")
assert(join(numeric_branch) == "0,12,2,14")
assert(join(numeric_nested) == "1112,1113,1213,1214,1314,1315")

print("loopvars: ok")
