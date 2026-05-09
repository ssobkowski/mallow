local function classifyPoint(x: number, y: number, z: number): string
    if x > 990  and x < 1150 and y > -500 and y < 125 and z > 1050 and z < 1350 then
        return "alpha"
    end
    if x > 60   and x < 180  and y > -500 and y < 130 and z > 1230 and z < 1400 then
        return "beta"
    end
    if x > -150 and x < 250  and y > -750 and y < 19  and z > 400  and z < 1200 then
        return "gamma"
    end
    if x > -50  and x < 150  and y > 18   and y < 40  and z > 600  and z < 1000 then
        return "delta"
    end
    if x > 637  and x < 811  and y > -750 and y < 70  and z > 2194 and z < 2407 then
        return "epsilon"
    end
    return "default"
end

print(classifyPoint(1070, 100,  1200))
print(classifyPoint(120,  100,  1300))
print(classifyPoint(50,   0,    800))
print(classifyPoint(50,   30,   800))
print(classifyPoint(720,  50,   2300))
print(classifyPoint(0,    0,    0))
print(classifyPoint(1150, 100,  1200))
