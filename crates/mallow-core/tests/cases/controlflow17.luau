local i = 0
local result = {}

repeat
    i = i + 1
    print("checking", i)

    if i == 4 then
        print("early-exit", i)
        break
    end

    table.insert(result, i)
until i >= 10

print("final", i, table.concat(result, ","))

local search = { "apple", "banana", "cherry", "date" }
local index = 0
local found_index = nil

repeat
    index = index + 1
    local item = search[index]
    print("search", index, item)

    if item == "cherry" then
        found_index = index
        break
    end
until index >= #search

print("found", found_index)
