local idx = 0
local p = 4
local step = {4, 1, 2, -2, 2}

repeat
    p = p + step[p % 6]
    local d = 1

    repeat
        d = d + step[d % 6]
        print("d", d)

        if d * d > p then
            idx = idx + 1
            break
        end

    until p % d == 0
until idx > 79

print("done")
