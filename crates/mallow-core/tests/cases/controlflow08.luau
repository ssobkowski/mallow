local function inspect(value)
    local score = 0

    if value % 2 == 0 then
        score += 10
        print(value, "even")
    end

    if value % 2 ~= 0 then
        score += 1
        print(value, "odd")
    end

    if value > 3 then
        score += 100
        print(value, "large")
    end

    if value < 0 then
        score += 1000
        print(value, "negative")
    end

    print("score", value, score)
end

for _, value in ipairs({ -2, 1, 4 }) do
    inspect(value)
end
