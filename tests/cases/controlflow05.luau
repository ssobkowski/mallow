local i = 0
local total = 0

while i < 8 do
    i = i + 1

    if i % 2 == 0 then
        continue
    end

    if i > 5 then
        break
    end

    total = total + i
    print("step", i, total)
end

print("done", i, total)
