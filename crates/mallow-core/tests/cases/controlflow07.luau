local function classify(value)
    if value < 0 then
        return "negative"
    end

    local label
    if value == 0 then
        label = "zero"
    else
        label = "positive"
    end

    print("fallthrough", value, label)
    return label
end

for _, value in ipairs({ -2, 0, 5 }) do
    print("result", value, classify(value))
end
