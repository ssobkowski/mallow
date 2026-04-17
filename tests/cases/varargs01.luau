local function sum(...)
    local total = 0
    for i = 1, select('#', ...) do
        total += select(i, ...)
    end
    return total
end

print(sum(1, 2, 3, 4, 5))
print(sum())
