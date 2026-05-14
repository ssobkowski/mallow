local i = 0
while i < 20 do
    if i % 2 == 0 then
        print("even", i)
    else
        print("uneven", i)
        i += 2
    end

    if i == 33 then
        break
    end

    i += 1

    if i == 100 then
        continue
    end
end

local j = 30
local flag = false
repeat
    while j % 2 == 0 do
        print("even", j)
        j += 3
    end

    if j % 2 == 0 then
        print("impossible")
    end

    if not flag and j > 35 then
        repeat
            j -= 5
        until j % 3 ~= 0
        flag = true
    end

    j += 1
until j >= 50
