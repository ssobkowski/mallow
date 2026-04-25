local function test(condition)
    for i = 1, 6 do
        if condition then
            for j = 1, 7 do
                print("then", i, j)
            end
        else
            for j = 1, 7 do
                print("else", i, j)
            end
        end
        print("shared", i)
    end
end

test(true)
test(false)
