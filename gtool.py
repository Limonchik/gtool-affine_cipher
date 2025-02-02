# gtool.py

# Генерация всех многочленов степени d над F_p
def generate_polynomials(p, d):
    result = []
    for i in range(p ** (d + 1)):
        poly = []
        value = i
        for _ in range(d + 1):
            poly.append(value % p)
            value //= p
        result.append(poly)
    return result

# Деление одного многочлена на другой по модулю p
def poly_div(dividend, divisor, p):
    dividend = dividend.copy()
    divisor = divisor.copy()
    
    if len(divisor) == 0:
        raise ValueError("Divisor must not be zero.")
    
    lead = divisor[0]
    if lead == 0:
        raise ValueError("Leading coefficient of divisor must be non-zero.")
    
    quotient = []
    dividend = [0] * (len(divisor) - 1) + dividend
    degree_diff = len(dividend) - len(divisor)
    
    for i in range(degree_diff + 1):
        curr_lead = dividend[i]
        if curr_lead == 0:
            quotient.append(0)
            continue
        factor = curr_lead * pow(lead, -1, p) % p
        quotient.append(factor)
        for j in range(len(divisor)):
            if i + j < len(dividend):
                dividend[i + j] = (dividend[i + j] - factor * divisor[j]) % p
    
    quotient = quotient[:degree_diff + 1]
    remainder = dividend[len(quotient):]
    return quotient, remainder

# Сложение двух многочленов по модулю p
def poly_add(poly1, poly2, p):
    max_len = max(len(poly1), len(poly2))
    poly1 = [0] * (max_len - len(poly1)) + poly1
    poly2 = [0] * (max_len - len(poly2)) + poly2
    return [(a + b) % p for a, b in zip(poly1, poly2)]

# Умножение двух многочленов по модулю p
def poly_mul(poly1, poly2, p):
    result = [0] * (len(poly1) + len(poly2) - 1)
    for i, a in enumerate(poly1):
        for j, b in enumerate(poly2):
            result[i + j] = (result[i + j] + a * b) % p
    return result

# Умножение в поле Галуа с приведением по модулю f
def poly_mult_GF(p, n, f, a, b):
    product = poly_mul(a, b, p)
    _, remainder = poly_div(product, f, p)
    if len(remainder) < n:
        remainder = [0] * (n - len(remainder)) + remainder
    return remainder

def galois_field(p, n, f=None):
    if p <= 1 or any(p % i == 0 for i in range(2, int(p ** 0.5) + 1)):
        raise ValueError("p must be a prime number.")
    
    def is_irreducible(poly):
        degree = len(poly) - 1
        for d in range(1, degree // 2 + 1):
            for divisor in generate_polynomials(p, d):
                if divisor[0] == 0:
                    continue
                _, remainder = poly_div(poly, divisor, p)
                if all(r == 0 for r in remainder):
                    return False
        return True
    
    if f is None:
        for poly in generate_polynomials(p, n):
            if poly[0] != 0 and is_irreducible(poly):
                f = poly
                break
        if f is None:
            raise ValueError("Unable to find an irreducible polynomial.")
    
    print(f"Неприводимый многочлен: {f}")
    
    # Генерация элементов без реверса коэффициентов
    num_elements = p ** n
    field = []
    for i in range(num_elements):
        element = []
        value = i
        for _ in range(n):
            element.append(value % p)
            value //= p
        field.append(element)
    return field, f

def galois_pow(element, exponent, f, p, n):
    """Возведение элемента в степень."""
    # Единичный элемент: [0, ..., 0, 1] (константа 1)
    result = [0] * (n-1) + [1]
    current = element.copy()
    while exponent > 0:
        if exponent % 2 == 1:
            result = poly_mult_GF(p, n, f, result, current)
        current = poly_mult_GF(p, n, f, current, current)
        exponent = exponent // 2
    return result

def find_element_order(element, p, n, f):
    zero_element = [0] * n
    one_element = [0] * (n-1) + [1]
    
    if element == zero_element:
        return None
    
    m = p ** n - 1
    for k in range(m, 0, -1):
        powered = galois_pow(element, k, f, p, n)
        if powered == one_element:
            for d in prime_factors(k):
                if galois_pow(element, k//d, f, p, n) == one_element:
                    break
            else:
                return k
    return None

def prime_factors(n):
    factors = []
    i = 2
    while i * i <= n:
        while n % i == 0:
            factors.append(i)
            n = n // i
        i += 1
    if n > 1:
        factors.append(n)
    return factors

def divisors(n):
    """Возвращает все делители числа n в отсортированном порядке."""
    factors = []
    i = 2
    while i*i <= n:
        while n % i == 0:
            factors.append(i)
            n //= i
        i += 1
    if n > 1:
        factors.append(n)
    
    # Генерация всех делителей
    divs = {1}
    for f in factors:
        divs |= {d*f for d in divs}
    return sorted(divs, reverse=True)

def parse_polynomial(input_str, p):
    """Преобразует строку ввода в многочлен с коэффициентами из F_p."""
    try:
        coeffs = list(map(int, input_str.strip().split()))
        return [c % p for c in coeffs]
    except:
        raise ValueError("Некорректный ввод многочлена")

# Реализация аффинного шифра над полем Галуа

def create_alphabet(p, n):
    """Создает алфавит, строго соответствующий размеру поля GF(p^n)."""
    field_size = p ** n
    base_alphabet = [
        'А', 'Б', 'В', 'Г', 'Д', 'Е', 'Ё', 'Ж', 'З', 'И', 'Й', 'К', 'Л', 'М', 
        'Н', 'О', 'П', 'Р', 'С', 'Т', 'У', 'Ф', 'Х', 'Ц', 'Ч', 'Ш', 'Щ', 'Ъ', 
        'Ы', 'Ь', 'Э', 'Ю', 'Я', ' ', '.', ',', '!', '?', '0', '1', '2', '3', 
        '4', '5', '6', '7', '8', '9'
    ]
    # Берем первые field_size символов
    return base_alphabet[:field_size]

def element_to_symbol(element, alphabet, p):
    """Преобразует элемент поля в символ алфавита."""
    # Элемент [a, b] интерпретируется как число в p-ичной системе: a*p^1 + b*p^0
    index = sum(coeff * (p ** i) for i, coeff in enumerate(reversed(element)))
    return alphabet[index % len(alphabet)]

def symbol_to_element(symbol, alphabet, p, n):
    """Преобразует символ в элемент поля Галуа."""
    try:
        index = alphabet.index(symbol)
    except ValueError:
        raise ValueError(f"Символ '{symbol}' не найден в алфавите")
    
    element = []
    value = index
    for _ in range(n):
        element.append(value % p)
        value //= p
    # Старшие коэффициенты идут первыми (например, [a, b] = a*x + b)
    return element[::-1]

def affine_encrypt(plaintext, alpha, beta, f, p, n, alphabet):
    """Зашифрование с проверкой символов."""
    filtered_text = []
    for char in plaintext:
        if char in alphabet:
            filtered_text.append(char)
        else:
            print(f"Пропущен символ '{char}' (отсутствует в алфавите)")
    if not filtered_text:
        raise ValueError("Нет символов для шифрования")
    
    ciphertext = []
    for char in filtered_text:
        elem = symbol_to_element(char, alphabet, p, n)
        encrypted = poly_add(poly_mult_GF(p, n, f, alpha, elem), beta, p)
        ciphertext.append(element_to_symbol(encrypted, alphabet, p))
    return ''.join(ciphertext)

def affine_decrypt(ciphertext, alpha, beta, f, p, n, alphabet):
    """Расшифрование с вычислением обратного элемента."""
    q = p**n - 1
    alpha_inv = galois_pow(alpha, q-1, f, p, n)  # α^{-1} = α^(q-1)
    
    plaintext = []
    for char in ciphertext:
        elem = symbol_to_element(char, alphabet, p, n)
        y_minus_beta = poly_add(elem, [(-b) % p for b in beta], p)
        decrypted = poly_mult_GF(p, n, f, y_minus_beta, alpha_inv)
        plaintext.append(element_to_symbol(decrypted, alphabet, p))
    return ''.join(plaintext)

if __name__ == "__main__":
    DEFAULT_P = 3
    DEFAULT_N = 2
    DEFAULT_IRR_POLY = [2, 1, 1]
    
    while True:
        action = input(
            "Выберите действие:\n"
            "1 - Исследовать поле Галуа\n"
            "2 - Операции с многочленами\n"
            "3 - Аффинный шифр\n"
            "> "
        ).strip()
        if action in ("1", "2", "3"):
            break
        print("Ошибка: введите 1, 2 или 3")

    try:
        p = input(f"Введите p (по умолчанию {DEFAULT_P}): ").strip()
        p = int(p) if p else DEFAULT_P
        
        n = input(f"Введите n (по умолчанию {DEFAULT_N}): ").strip()
        n = int(n) if n else DEFAULT_N
        
        irr_poly_input = input(
            f"Введите неприводимый многочлен степени {n} (по умолчанию {DEFAULT_IRR_POLY}): "
        ).strip()
        
        if irr_poly_input:
            irr_poly = parse_polynomial(irr_poly_input, p)
            if len(irr_poly) != n+1:
                raise ValueError(f"Многочлен должен иметь степень {n}")
        else:
            irr_poly = DEFAULT_IRR_POLY.copy()
            
        field, f = galois_field(p, n, irr_poly)
        print(f"\nПоле GF({p}^{n}) с многочленом {f}")
        
    except Exception as e:
        print(f"Ошибка: {e}")
        exit()

    if action == "1":
        print("\nЭлементы поля с порядками:")
        for elem in field:
            order = find_element_order(elem, p, n, f)
            if order is None:
                print(f"{elem}: нулевой элемент")
            else:
                labels = []
                if 1 < order < p**n-1 :
                    labels.append("Образующий подгруппы")
                print(f"{elem}: порядок {order}" + (" (" + ", ".join(labels) + ")" if labels else ""))

    elif action == "2":
        def input_element(name: str) -> list[int]:
            while True:
                try:
                    s = input(f"Введите элемент {name}: ").strip()
                    coeffs = parse_polynomial(s, p)
                    if len(coeffs) > n:
                        raise ValueError("Степень элемента превышает n-1")
                    return coeffs + [0]*(n - len(coeffs))
                except Exception as e:
                    print(f"Ошибка: {e}")

        elem1 = input_element("A")
        elem2 = input_element("B")
        op = input("Выберите операцию (+, *): ").strip()
        
        try:
            if op == "+":
                result = poly_add(elem1, elem2, p)
            elif op == "*":
                result = poly_mult_GF(p, n, f, elem1, elem2)
            else:
                print("Недопустимая операция")
                exit()
                
            print(f"\nРезультат {op}: {result}")
        except Exception as e:
            print(f"Ошибка: {e}")

    elif action == "3":
        alphabet = create_alphabet(p, n)
        print(f"\nАлфавит ({len(alphabet)} символов): {''.join(alphabet)}")

        def input_key_element(name: str) -> list[int]:
            while True:
                try:
                    s = input(f"Введите {name} (степень < {n}): ").strip()
                    coeffs = parse_polynomial(s, p)
                    if len(coeffs) > n:
                        raise ValueError("Степень элемента превышает n-1")
                    return coeffs + [0]*(n - len(coeffs))
                except Exception as e:
                    print(f"Ошибка: {e}")

        print("\nВвод ключа:")
        alpha = input_key_element("α")
        beta = input_key_element("β")
        
        if all(c == 0 for c in alpha):
            print("Ошибка: α не может быть нулём")
            exit()

        while True:
            operation = input(
                "Выберите операцию:\n"
                "1 - Зашифровать\n"
                "2 - Расшифровать\n"
                "> "
            ).strip()
            if operation in ("1", "2"):
                break
            print("Ошибка: введите 1 или 2")

        text = input("Введите текст: ").upper()
        # Фильтрация символов
        filtered_text = []
        for char in text:
            if char in alphabet:
                filtered_text.append(char)
            else:
                print(f"Предупреждение: символ '{char}' отсутствует в алфавите и будет пропущен.")
        text = ''.join(filtered_text)
        if not text:
            print("Ошибка: после фильтрации текст пуст.")
            exit()

        try:
            if operation == "1":
                result = affine_encrypt(text, alpha, beta, f, p, n, alphabet)
                print(f"\nШифртекст: {result}")
            else:
                result = affine_decrypt(text, alpha, beta, f, p, n, alphabet)
                print(f"\nРасшифрованный текст: {result}")
        except Exception as e:
            print(f"Ошибка: {e}")