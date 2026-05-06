local function run(has_predicate)
    local state = {
        step = 0,
    }

    local function tick()
        return state.step
    end

    local function predicate(value)
        print("predicate", has_predicate, value)
        return value ~= 2
    end

    while tick() < 4 and (not has_predicate or predicate(tick())) do
        print("body", has_predicate, state.step)
        state.step += 1
    end

    print("done", has_predicate, state.step)
end

run(false)
run(true)
