def print_c(text, color='white', style='normal'):
    # ANSI 转义序列颜色代码
    colors = {
        'black': '30', 'red': '31', 'green': '32', 'yellow': '33',
        'blue': '34', 'magenta': '35', 'cyan': '36', 'white': '37',
        'bright_black': '90', 'bright_red': '91', 'bright_green': '92',
        'bright_yellow': '93', 'bright_blue': '94', 'bright_magenta': '95',
        'bright_cyan': '96', 'bright_white': '97'
    }

    # ANSI 转义序列样式代码
    styles = {
        'normal': '0', 'bold': '1', 'underline': '4', 'reverse': '7', 'hidden': '8',
        'blink': '5', 'dim': '2', 'reset': '0', 'italic': '3'
    }

    # 获取颜色和样式的代码
    color_code = colors.get(color, '37')  # 默认白色
    style_code = styles.get(style, '0')  # 默认正常

    # 拼接颜色和样式的转义序列
    start_code = f"\033[{style_code};{color_code}m"
    end_code = "\033[0m"

    # 打印带颜色的文本
    print(f"{start_code}{text}{end_code}")
