local value = 1
local seen = {}

repeat
    table.insert(seen, value)
    value = value * 2
until value > 16

print(table.concat(seen, ","))
print(value)
