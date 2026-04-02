local i = 0
local tag = "start"

repeat
    i = i + 1

    if i % 2 == 0 then
        tag = "even"
    else
        tag = "odd"
    end

    print("loop", i, tag)
until i >= 5

if tag == "odd" then
    print("done-odd", i)
else
    print("done-even", i)
end
