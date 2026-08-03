local function through_join(value, gate)
    if value then
        if gate then
            print(value)
        end
        return value
    end
    return 0
end

print(through_join(1, true), through_join(nil, false))
