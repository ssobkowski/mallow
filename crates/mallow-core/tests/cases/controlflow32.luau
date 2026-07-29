local function prefix_find(t: {string}, p: string, exclude: {string}): string?
    for _, v in t do
        if v:sub(1, #p) == p and not table.find(exclude, v) then
            return v
        end
    end
    return nil
end

local t = { "apple", "banana", "coke", "cherry", "date", "cake", "chocolate" }
local diabetic = { "cake", "chocolate", "coke" }
print(prefix_find(t, "ap", diabetic))
print(prefix_find(t, "ban", diabetic))
print(prefix_find(t, "co", diabetic))
print(prefix_find(t, "dat", diabetic))
