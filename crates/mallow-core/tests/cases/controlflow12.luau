local i = 0
local total = 0

while i < 6 do
    i = i + 1

    local contribution
    if i % 2 == 0 then
        contribution = i * 10
    else
        contribution = -i
    end

    total = total + contribution
    print("step", i, contribution, total)
end

print("final", total)
