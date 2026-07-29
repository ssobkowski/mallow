local i = 0
local collected = {}

repeat
    i = i + 1

    if i % 2 == 0 then
        print("skip-even", i)
        continue
    end

    table.insert(collected, i)
    print("collect", i)
until i >= 8

print("result", table.concat(collected, ","))

local n = 0
local sum = 0

repeat
    n = n + 1

    if n == 3 then
        print("skip-three", n)
        continue
    end

    if n > 6 then
        print("done-at", n)
        break
    end

    sum = sum + n
    print("add", n, sum)
until n >= 10

print("final", n, sum)
