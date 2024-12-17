def check_interval(num, intervals):
    """
    检查数值是否在区间列表中，输出对应区间的索引（从0开始），
    若不在任何区间内，则输出-1。

    :param num: 需要检查的数值
    :param intervals: 区间列表，每个区间由元组表示，格式为 (start, end, left_open, right_open)
                      start: 区间的起始值
                      end: 区间的结束值
                      left_open: 左端点是否开区间，True表示开，False表示闭
                      right_open: 右端点是否开区间，True表示开，False表示闭
    :return: 区间的索引或-1
    """
    for index, (start, end, left_open, right_open) in enumerate(intervals):
        if num < start or num > end:
            continue

        if left_open and num == start:
            continue
        if right_open and num == end:
            continue

        # 如果都符合要求，说明num在当前区间内
        return index

    # 如果遍历所有区间后都没有找到，返回-1
    return -1


# 示例区间列表
# intervals = [
#     (0.5, 0.75, True, True),  # (0.5, .75) 开区间
#     (1, 5, False, False),  # [1, 5] 闭区间
#     (3, 7, True, False),   # (3, 7] 左开右闭区间
#     (10, 20, False, True), # [10, 20) 左闭右开区间
#     (8, 12, True, True)    # (8, 12) 左右开区间
# ]
#
# # 测试不同的数值
# test_values = [0.5, 0.75, 1, 5, 3, 7, 10, 20, 8, 12, 4, 6, 12, 19, 3, 5, 8, 7, 15, 2]
#
# for num in test_values:
#     index = check_interval(num, intervals)
#     if index != -1:
#         print(f"Number {num} is in interval at index {index}.")
#     else:
#         print(f"Number {num} is not in any interval.")

def is_intersecting(interval1, interval2):
    """
    判断两个区间是否相交，并返回相交的区间。

    :param interval1: 第一个区间 (start1, end1, left_open1, right_open1)
    :param interval2: 第二个区间 (start2, end2, left_open2, right_open2)
    :return: 相交的区间，如果没有相交返回 None
    """
    start1 = interval1[0]
    start2 = interval2[0]
    if start1 <= start2:
        start1, end1, left_open1, right_open1 = interval1
        start2, end2, left_open2, right_open2 = interval2
    else:
        start1, end1, left_open1, right_open1 = interval2       # swap such that the smaller one will be the first
        start2, end2, left_open2, right_open2 = interval1

    if (start1 < start2 and end1 < start2) or (end2 < start1 and start2 < start1):
        #
        # 逆向思维
        # 先排除完全不相交的情形
        return False, None
    elif end1 == start2 and (right_open1 == True or left_open2 == True):
        return False, None
    elif end2 == start1 and (right_open2 == True or left_open1 == True):
        return False, None

    # 计算交集区间的起点和终点
    intersect_start = max(start1, start2)
    intersect_end = min(end1, end2)

    # 判断交集区间的开闭性
    if intersect_start == start1 and left_open1:
        intersect_left_open = True
    elif intersect_start == start2 and left_open2:
        intersect_left_open = True
    else:
        intersect_left_open = False

    if intersect_end == end1 and right_open1:
        intersect_right_open = True
    elif intersect_end == end2 and right_open2:
        intersect_right_open = True
    else:
        intersect_right_open = False

    # 返回交集区间及其开闭性
    return True, (intersect_start, intersect_end, intersect_left_open, intersect_right_open)

def is_connected(interval1, interval2):
    start1 = interval1[0]
    start2 = interval2[0]
    if start1 <= start2:
        start1, end1, left_open1, right_open1 = interval1
        start2, end2, left_open2, right_open2 = interval2
    else:
        start1, end1, left_open1, right_open1 = interval2       # swap such that the smaller one will be the first
        start2, end2, left_open2, right_open2 = interval1

    if end1 == start2:
        if right_open1 == False or left_open2 == False:
            return True
        else:
            return  False


def is_subset(interval1, interval2):
    start1, end1, left_open1, right_open1 = interval1
    start2, end2, left_open2, right_open2 = interval2

    # Check if the intervals do not overlap
    if (end1 < start2) or (end2 < start1):
        return False

    # Check if the intervals are adjacent and open at the boundary
    if (end1 == start2 and (right_open1 or left_open2)) or (end2 == start1 and (right_open2 or left_open1)):
        return False

    # Now check if interval1 is a subset of interval2
    # Interval1 is a subset of Interval2 if:
    # 1. start1 >= start2 (interval1 starts at or after interval2)
    # 2. end1 <= end2 (interval1 ends at or before interval2)
    # 3. The open/closed conditions must also be respected

    if start1 > start2 or (start1 == start2 and not left_open2) or (start1 == start2 and (left_open1 and left_open2)):
        is_left_satisfied = True
    else:
        is_left_satisfied = False

    if end1 < end2 or (end1 == end2 and not right_open2) or (end1 == end2 and (right_open1 and right_open2)):
        is_right_satisfied = True
    else:
        is_right_satisfied = False

    if is_left_satisfied and is_right_satisfied:
        return True
    else:
        return False


# Example usage:
# interval1 = (2, 6, True, True)  # (2, 6)
# interval2 = (0, 6, False, True)  # [0, 6)
#
# result = is_subset(interval1, interval2)
# print("interval1 is the subset of interval 2? %s" % (str(result), ))  # True or False

def check_intersection_with_list(query_interval, interval_list):
    """
    判断给定区间 query_interval 是否和区间列表中的某个区间相交。
    :param query_interval: 给定的查询区间 (start, end, left_open, right_open)
    :param interval_list: 区间列表，每个区间由元组表示 (start, end, left_open, right_open)
    :return: 相交的区间索引及交集区间，如果没有相交返回 (-1, None)
    """
    for index, interval in enumerate(interval_list):
        is_intersect, intersect_interval = is_intersecting(query_interval, interval)
        if is_intersect:
            return index, intersect_interval
    return -1, None


# 示例区间列表
# intervals = [
#     (1, 5, False, False),  # [1, 5] 闭区间
#     (3, 7, True, False),   # (3, 7] 左开右闭区间
#     (10, 20, False, True), # [10, 20) 左闭右开区间
#     (8, 12, True, True)    # (8, 12) 左右开区间
# ]
#
# # 查询区间
# query_interval = (4, 8, False, True)  # [4, 8) 左闭右开区间
#
# # 测试
# index, intersect_interval = check_intersection_with_list(query_interval, intervals)
# if index != -1:
#     print(f"Query interval intersects with interval at index {index}: {intersect_interval}")
# else:
#     print("No intersection found.")

def intersection_of_half_open_intervals(intervals, left_open, right_open):
    """
    计算多个区间的交集，支持指定每个区间的开闭性。

    :param intervals: 区间列表，每个区间是一个元组 (start, end)。
    :param left_open: 布尔值列表，表示每个区间的左端是否开区间，True 表示开，False 表示闭。
    :param right_open: 布尔值列表，表示每个区间的右端是否开区间，True 表示开，False 表示闭。
    :return: 区间的交集列表，返回每个交集区间的开闭信息。
    """
    if not intervals:
        return []

    # 初始化交集区间为第一个区间
    current_interval = (intervals[0][0], intervals[0][1], left_open[0], right_open[0])

    for i in range(1, len(intervals)):
        # 计算当前区间与下一区间的交集
        is_intersect, intersected_interval = is_intersecting(current_interval, (intervals[i][0], intervals[i][1], left_open[i], right_open[i]))

        if not is_intersect:
            # 如果没有交集，返回空列表（表示没有交集）
            return []

        # 更新交集区间
        current_interval = intersected_interval

    # 返回所有区间的交集
    return [current_interval]


# 示例测试
# intervals =  [(1, 5), (2, 6), (4, 7), (3, 8)]
# left_open =  [True,  True, False, True]
# right_open = [False, True, True,  False]                 # True为开, False为闭
#
# # 计算交集
# result = intersection_of_half_open_intervals(intervals, left_open, right_open)
#
# # 输出结果
# for interval in result:
#     print(interval)  # 打印交集区间及其开闭性


def union_of_half_open_intervals(intervals, left_open, right_open):
    """
    计算多个区间的并集，支持指定每个区间的开闭性。

    :param intervals: 区间列表，每个区间是一个元组 (start, end)。
    :param left_open: 布尔值列表，表示每个区间的左端是否开区间，True 表示开区间，False 表示闭区间。
    :param right_open: 布尔值列表，表示每个区间的右端是否开区间，True 表示开区间，False 表示闭区间。
    :return: 合并后的区间列表，返回每个区间的开闭信息
    """
    if not intervals:
        return []

    # 按区间的起始值排序，同时保留开闭性信息
    intervals = sorted(zip(intervals, left_open, right_open), key=lambda x: x[0][0])
    merged_intervals = []

    for (start, end), left, right in intervals:
        # 如果 merged_intervals 为空，直接添加第一个区间
        if not merged_intervals:
            merged_intervals.append((start, end, left, right))
            continue

        # 获取当前区间和上一个区间的信息
        prev_start, prev_end, prev_left, prev_right = merged_intervals[-1]

        is_intersect, intersected_interval = is_intersecting([prev_start, prev_end, prev_left, prev_right], [start, end, left, right])

        # 判断两个区间是否有交集或相邻
        # if (prev_end > start) or (prev_end == start and (prev_right or left)):
        if is_intersect:
            # 交集或者相邻区间，合并
            new_start = min(prev_start, start)
            new_end = max(prev_end, end)

            # 合并时更新开闭区间的状态
            if prev_start == start:
                if prev_left == True and left == True:
                    new_left_open = True
                else:
                    new_left_open = False
            else:
                new_left_open = prev_left if prev_start < start else left
            #
            if prev_end == end:
                if prev_right == True and right == True:
                    new_right_open = True
                else:
                    new_right_open = False
            else:
                new_right_open = prev_right if prev_end > end else right

            # 更新merged_intervals中的最后一个区间
            merged_intervals[-1] = (new_start, new_end, new_left_open, new_right_open)
        elif prev_end == start and (prev_right == False or left == False):
            # if the two intervals are connected
            merged_intervals[-1] = (prev_start, end, prev_left, right)
        else:
            # 没有交集，直接添加当前区间
            merged_intervals.append((start, end, left, right))

    # 返回合并后的区间，包括开闭性信息
    return [(start, end, left, right) for start, end, left, right in merged_intervals]


# # 测试
# intervals  = [(-1, 0.5), (10, 20), (1, 5), (2, 6), (4, 7), (3, 8), (10, 29)]
# left_open  = [False, True, False, True, False, True,  False]      # [-1, 0.5), (10,20), [1,5], (2,6), [4,7), (3,8], [10, 29)
# right_open = [True,  True, False, True, True,  False, True]
# # 测试组 2
# intervals  = [(1, 3), (3, 4), (4, 10)]
# left_open  = [False, False, False]      # [1, 3), [3, 4), [4, 10)
# right_open = [True,  True, True]
#
# # 合并区间
# merged_intervals = union_of_half_open_intervals(intervals, left_open, right_open)
#
# # 输出合并后的区间
# for interval in merged_intervals:
#     print(interval)
