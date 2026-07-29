local function read_value(table)
    return table.value
end

local table = {}
print(read_value(table))
table.value = 42
print(read_value(table))
