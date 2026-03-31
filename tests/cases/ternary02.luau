local function choose(flag, yes, no, label)
    local value = if flag then yes else no
    print(label, value)
end

choose(true, false, "no", "true_false")
choose(true, nil, "no", "true_nil")
choose(false, "yes", "no", "false_string")
choose(false, nil, false, "false_false")
