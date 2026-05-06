local function run(ready_at)
    local state = {
        live = true,
    }
    local probes = 0

    local function next_item()
        probes += 1
        print("probe", ready_at, probes)
        if probes >= ready_at then
            return {
                id = probes,
            }
        end
        return nil
    end

    while state.live and not next_item() do
        print("wait", ready_at, probes)
        if probes > 5 then
            state.live = nil
        end
    end

    if state.live then
        print("ready", ready_at, probes)
    else
        print("gone", ready_at, probes)
    end
end

run(1)
run(3)
run(9)
