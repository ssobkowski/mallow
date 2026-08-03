local function nested_truthiness(value)
    if value then
        if value then
            return value
        else
            return "unreachable"
        end
    end
    return 0
end

print(nested_truthiness(1), nested_truthiness(nil))
