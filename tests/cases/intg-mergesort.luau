local merge = {}

function merge.sort(array)
	local function mergeSort(low, mid, high)
		local n1 = mid - low + 1
		local n2 = high - mid
		local left = {}
        local right = {}

		for i = 1, n1 do
			left[i] = array[low + i - 1]
		end
		left[n1 + 1] = math.huge

		for j = 1, n2 do
			right[j] = array[mid + j]
		end
		right[n2 + 1] = math.huge

		local i = 1
		local j = 1

		for k = low, high do
			if left[i] <= right[j] then
				array[k] = left[i]
				i += 1
			else
				array[k] = right[j]
				j += 1
			end
		end
	end

	local function sort(low, high)
		if low < high then
			local mid = math.floor((low + high) / 2)
			sort(low, mid)
			sort(mid + 1, high)
			mergeSort(low, mid, high)
		end

		return array
	end

	return sort(1, #array)
end

local nums = {642, 942, 174, 482, 289, 901, 805, 913, 604, 415, 332, 503, 393, 367, 351, 663, 860, 141, 713, 711, 610, 329, 384, 297, 600, 614, 927, 731, 422, 266, 673, 530, 231, 514, 889, 526, 521, 470, 290, 784, 706, 251, 211, 861, 885, 919, 830, 524, 529, 465, 827, 177, 856, 347, 715, 868, 721, 389, 609, 343, 398, 730, 317, 940, 766, 933, 401, 227, 360, 763, 671, 820, 999, 900, 705, 959, 561, 477, 368, 462, 165, 824, 708, 911, 771, 502, 816, 921, 494, 969, 154, 564, 162, 179, 712, 753, 847, 700, 896, 651}
print(table.concat(nums, ","))

merge.sort(nums)
print(table.concat(nums, ","))
