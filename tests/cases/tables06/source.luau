local empty = {}
print(#empty)
print(type(empty))

local single_array = {42}
local single_hash = {key = "value"}
print(single_array[1])
print(single_hash.key)

local mixed = {
    a = 1,
    [2] = "two",
    b = 3,
    [4] = "four",
    "five"
}
print(mixed.a)
print(mixed[2])
print(mixed.b)
print(mixed[4])
print(mixed[1])

local same = {7, 7, 7, 7, 7}
print(table.concat(same, ","))

local confusing = {
    ["if"] = "reserved keyword",
    ["continue"] = "not a reserved keyword",
    ["local"] = "reserved keyword"
}
print(confusing["if"] == confusing["local"] and confusing["if"] ~= confusing["continue"])

local expr_values = {
    1 + 1,
    2 * 3,
    10 / 2,
    x = 5 + 5,
    y = 3 * 3
}
print(expr_values[1])
print(expr_values[2])
print(expr_values[3])
print(expr_values.x)
print(expr_values.y)
