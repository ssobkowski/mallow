local function purely_unhinged_flow(seed: number): string
    local state: number, acc: number, flag: boolean = seed % 10, 0, false
    local entropy: {number} = {1, 2, 3, 4, 5}

    local function convolute(val: number)
        -- Returns a function based on a short-circuit evaluation
        return (if val > 5 then function(x) return x * (if val % 2 == 0 then -1 else 1) end
            else function(x) return x + val end)
    end

    while not flag do
        if state == 0 or state == 7 then
            for i = 1, #entropy do
                -- In-line evaluation, ternary abuse, and function calls inside arithmetic
                acc += (if i % 2 == 0 then (if entropy[i] > 2 then convolute(entropy[i])(acc) else -entropy[i])
                    else 0) + (if entropy[i] == 3 then 10 else 0)

                if acc > 100 then
                    state = 1
                    break
                elseif acc < -50 then
                    continue
                end

                entropy[i] = acc % 5
            end
            state = if state == 0 then 2 else 3

        elseif state == 1 then
            repeat
                acc /= 2
                -- State mutation inside a short-circuit assignment
                state = if acc < 10 then 4 else 5
            until state ~= 1 or (function()
                -- Anonymous function executed solely to evaluate a repeat-until condition
                return acc % 3 == 0
            end)()

            if state == 1 then state = 2 end

        elseif state == 2 then
            local dummy: number = 0
            while dummy < 10 do
                dummy += (dummy % 4 == 0 and 2 or 1)
                if dummy == 6 then
                    -- The ultimate sin: side-effects inside a dummy assignment short-circuit
                    local _ = (if acc > 0 then (function() state = 3; return true end)()
                        else (function() state = 4; return false end)())
                    break
                end
            end

        elseif state == 3 or state == 4 then
            -- Boolean assignment based on cross-state short-circuiting
            flag = (if state == 3 then acc % 2 == 0 else false)
                or (if state == 4 then acc < 0 else false)
            state = 5

        else
            local matrix = {}
            for j = 1, 3 do
                matrix[j] = (if j == 1 then (if state == 5 then "X" else "Y")
                    else if j == 2 then (if flag then "T" else "F")
                    else "Z")
            end

            if matrix[1] == "X" and not flag then
                state = 0
                acc += 1
            else
                flag = true
            end
        end
    end

    return (if acc > 0 then "Survived: " else "Crushed: ") .. tostring(acc)
end

-- Have fun reading the bytecode.
print(purely_unhinged_flow(42))
