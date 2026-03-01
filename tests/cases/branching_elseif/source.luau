local function classify(value)
    if value < 0 then
        return "negative"
    elseif value == 0 then
        return "zero"
    elseif value % 2 == 0 then
        return "even"
    else
        return "odd"
    end
end

for _, value in ipairs({ -3, 0, 4, 7 }) do
    print(value, classify(value))
end
