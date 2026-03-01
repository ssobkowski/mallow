local rows = {
    { 1, 2, 3 },
    { 4, 5 },
    { 6 },
}

for row_index, row in ipairs(rows) do
    local row_total = 0

    for column_index, value in ipairs(row) do
        if column_index % 2 == 0 then
            row_total = row_total + value * 2
        else
            row_total = row_total + value
        end
    end

    print("row", row_index, row_total)
end
