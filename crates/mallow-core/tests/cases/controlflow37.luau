local function collect(first, last)
    local result = {}

    if first <= last then
        for index = math.max(first, 1), math.min(last, 5) do
            table.insert(result, index)
        end
    else
        for index = math.min(first, 5), math.max(last, 1), -1 do
            table.insert(result, index)
        end
    end

    return result
end

local callback = select(1, collect) -- black box
print(table.concat(callback(-2, 3), ","))
print(table.concat(callback(5, 3), ","))
