for i = 1, 6 do
    if i % 2 == 0 then
        if i % 3 == 0 then
            print(i, "six")
        else
            print(i, "even")
        end
    elseif i == 5 then
        print(i, "five")
    else
        print(i, "odd")
    end
end
