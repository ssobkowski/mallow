local function dream_loop(a: number)
    local b = 0

    while (a <= 1 and b <= 100) or (a > 1 and b <= 100) do
        print("inside loop", a, b)
        b += 1
        a -= 1
    end

    print("loop terminated")
    return b
end

print(dream_loop(67))
