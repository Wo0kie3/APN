# ***************************************************************************************************************************#
# *********************************************************Formuły***********************************************************#
# ***************************************************************************************************************************#

form1 = ['iff', ['or', 'A', 'B'], ['and', ['not', 'A'], 'C']]
form2 = ['imp', ['imp', ['and', 'P', 'Q'], 'R'], ['imp', 'P', 'R']]
form3 = ['and', ['not', 'A'], 'A']
form4 = ['not', ['imp', ['and', 'P', ['or', 'Q', 'R']], ['or', ['and', 'P', 'Q'], 'R']]]
form5 = ['and', 'A', ['or', 'B', 'C']]
form6 = ['iff',['imp','P','R'],['and',['not','P'],'R']]
form7 = ['imp', ['imp', ['and', 'P', 'Q'], 'R'], ['imp', 'P', ['imp', 'Q', 'R']]]
form8 = ['not',['or',['iff','P','Q'],['imp','P',['or','Q','P']]]]
form9 = ['imp',['iff','P',['not','R']],['imp',['and','P','Q'],'R']]
form10 = ['iff',['not',['imp','P','Q']],['and','P',['not','Q']]]

# ***************************************************************************************************************************#
# ***********************************************Sprawdzanie Poprawności*****************************************************#
# ***************************************************************************************************************************#

# -----------------------------------------------#
# Sprawdzanie implikacji
# -----------------------------------------------#
def impKandydat(formula):
    if formula[0] == 'imp' and len(formula) == 3:
        return True
    else:
        return False


# -----------------------------------------------#
# Sprawdzanie równoważności
# -----------------------------------------------#
def iffKandydat(formula):
    if formula[0] == 'iff' and len(formula) == 3:
        return True
    else:
        return False


# -----------------------------------------------#
# Sprawdzanie negacji
# -----------------------------------------------#
def notKandydat(formula):
    if formula[0] == 'not' and len(formula) == 2 and len(formula[1]) != 1:
        return True
    else:
        return False


# -----------------------------------------------#
# Sprawdzanie or i and
# -----------------------------------------------#
def rozkladKandydat(formula):
    if formula[0] == 'and':
        for i in range(1, len(formula)):
            if len(formula[i]) > 1:
                if formula[i][0] == 'or':
                    return True
    return False


# ******************************************************Metody wewnetrzene*******************************************************#

# ------------------------------------------------------#
# usuwanie niepotrzebnych duplikatów formuł i list
# upraszcza zdanie do postaci
# [or, [or a b], [or c d]] => [or a b c d]
# ------------------------------------------------------#
def czyszczenie(formula):
    result = []

    # Sprawdzamy czy logika jest negacją
    # Jeśli tak to nic nie robimy
    if formula[0] == 'not':
        return formula

    # dodawanie logiki
    result.append(formula[0])
    outLogic = formula[0]

    # pętla przchodząca przez formułe
    for i in range(1, len(formula)):
        # sprawdzanie czy logika wyjsciowa jest taka sama jak wejsciowa
        if formula[i][0] == outLogic:
            # dodawanie literałów listy
            for j in range(1, len(formula[i])):
                result.append(formula[i][j])
        else:
            # dodajemy logikę bez zmian
            result.append(formula[i])

    return result


# ------------------------------------------------------#
# Zamiana formuły do postaci gdzie operator ma tylko dwa literały
# or(a b c d) = or(or(or(a b) c) d)
# ------------------------------------------------------#
def upraszczanieMetod(operator, literal, current):
    result = []
    result.append(operator)
    # Jeśli literał jest jeden dodaj literał jeśli nie rekurencyjnie upraszczaj
    if len(literal) == 1:
        result.append(literal[0])
    else:
        result.append(upraszczanieMetod(operator, literal[0:len(literal) - 1], literal[len(literal) - 1]))

    # dodawanie bierzącej formuły
    result.append(current)

    return result


# ------------------------------------------------------#
# Upraszczanie formuly i wszystkich pod-formul
# ------------------------------------------------------#
def upraszczanie(formula):
    # upraszacznie jeśli wiecej niż 3 literały
    if len(formula) > 3:
        formula = upraszczanieMetod(formula[0], formula[1:len(formula) - 1], formula[len(formula) - 1])

    # rekurencyjne upraszczanie logik w środku
    for i in range(1, len(formula)):
        if len(formula[i]) > 1:
            formula[i] = upraszczanie(formula[i])

    if len(formula) > 3:
        formula = upraszczanieMetod(formula[0], formula[1:len(formula) - 1], formula[len(formula) - 1])

    return formula


# ------------------------------------------------------#
# Spawdzanie czy dwie logiki są równe
# ------------------------------------------------------#
def czyRowne(logic1, logic2):
    # Jeśli długość jest różna są różne
    if len(logic1) != len(logic2):
        return False
    else:
        # jeśli obie są zmiennymi
        if len(logic1) == len(logic2) == 1:
            if logic1 == logic2:
                return True
            else:
                return False
        else:
            # Jeśli obie są zdaniami składowymi
            # tworzenie tymczasowej listy
            temp = list(logic2)
            for element in logic1:
                try:
                    # staramy się usuwać takie same elementy jeśli istnieją
                    temp.remove(element)
                except ValueError:
                    return False

            # zwraca pustą liste albo False
            # jeśli temp jest pusty oba są równe
            return not temp


# ------------------------------------------------------#
# Sprawdzanie czy logika jest taka sama jak w rodzicu
# ------------------------------------------------------#
def rodzicLogic(result, formula):
    for i in range(1, len(result)):
        # Sprawdzanie czy jest równa do jakiejkolwiek logiki
        if czyRowne(result[i], formula):
            return True
    return False


# ***************************************************************************************************************************#
# *********************************************************RULES*************************************************************#
# ***************************************************************************************************************************#


# ------------------------------------------------------#
# usuwanie implikacji poprzez
# A => B zmieniamy na ~A V B
# ------------------------------------------------------#
def usuwanieIMP(formula):
    result = []
    result.append('or')
    result.append(['not', formula[1]])
    result.append(formula[2])

    return result


# ------------------------------------------------------#
# usuwanie równoważności poprzez
# A <=> B zamieniamy na (A=>B)^(B=>A)
# ------------------------------------------------------#
def usuwanieIFF(formula):
    result = []
    result.append('and')
    result.append(usuwanieIMP(['imp', formula[1], formula[2]]))
    result.append(usuwanieIMP(['imp', formula[2], formula[1]]))

    return result


# ------------------------------------------------------#
# Prawa De Morgana
# ~(A V B) = ~A ^ ~B
# ~(A ^ B) = ~A V ~B
# ------------------------------------------------------#
def deMorganZamiana(formula):
    result = []

    # sprawdzamy operato i dodajemy przeciwny or na and i and na or
    if (formula[1][0] == 'or'):
        result.append('and')
    elif (formula[1][0] == 'and'):
        result.append('or')
    # jeśli logika jest negacja zwracamy sam literał
    elif (formula[1][0] == 'not'):
        return formula[1][1]

    # sprawdzamy argumenty wewnętrzne
    for i in range(1, len(formula[1])):
        # sprawdzamy czy pierwszy argument jest inną listą
        if len(formula[1][i]) != 1:
            # rekurencyjne robienie de morgana jeśli argument jest listą
            result.append(deMorganZamiana(['not', formula[1][i]]))
        else:
            # jeśli nie to wstawiamy negacje literału
            result.append(['not', formula[1][i]])

    return result


# ------------------------------------------------------#
# Wyprowadznie alternatywy przed koniungcje
# P ^ (Q v R) = (P ^ Q) v (P ^ R)
# ------------------------------------------------------#
def rozkladAND(formula):
    result = []
    # stawiamy operator na początku
    result.append('or')

    # sprawdzanie czy obie listy są or
    if formula[1][0] == 'or' and formula[2][0] == 'or':
        # rozkładanie literałów
        result.append(rozkladFormulyORAND(['and', formula[1][1], formula[2][1]]))
        result.append(rozkladFormulyORAND(['and', formula[1][1], formula[2][2]]))
        result.append(rozkladFormulyORAND(['and', formula[1][2], formula[2][1]]))
        result.append(rozkladFormulyORAND(['and', formula[1][2], formula[2][2]]))

    else:
        # kiedy przynajmniej jedna jest or
        if formula[1][0] == 'or':

            # sprawdzamy czy drugi argument jest litą
            if len(formula[2]) > 2:
                # sprawdzamy czy można go rozłożyć
                if rozkladKandydat(formula[2]):
                    formula[2] = rozkladFormulyORAND(formula[2])

                    # rozkładanie
                    result.append(rozkladFormulyORAND(['and', formula[1][1], formula[2][1]]))
                    result.append(rozkladFormulyORAND(['and', formula[1][1], formula[2][2]]))
                    result.append(rozkladFormulyORAND(['and', formula[1][2], formula[2][1]]))
                    result.append(rozkladFormulyORAND(['and', formula[1][2], formula[2][2]]))

                else:
                    # jeśli nie zostawiamy go
                    result.append(rozkladFormulyORAND(['and', formula[1][1], formula[2]]))
                    result.append(rozkladFormulyORAND(['and', formula[1][2], formula[2]]))

            else:
                # jeśli nie zostawiamy go
                result.append(rozkladFormulyORAND(['and', formula[1][1], formula[2]]))
                result.append(rozkladFormulyORAND(['and', formula[1][2], formula[2]]))
        else:

            # sprawdzamy czy pierwszy argument jest litą
            if len(formula[1]) > 2:
                # sprawdzamy czy można go rozłożyć
                if rozkladKandydat(formula[1]):
                    formula[1] = rozkladFormulyORAND(formula[1])

                    # rozkładanie
                    result.append(rozkladFormulyORAND(['and', formula[1][1], formula[2][1]]))
                    result.append(rozkladFormulyORAND(['and', formula[1][1], formula[2][2]]))
                    result.append(rozkladFormulyORAND(['and', formula[1][2], formula[2][1]]))
                    result.append(rozkladFormulyORAND(['and', formula[1][2], formula[2][2]]))
                else:
                    # jeśli nie zostawiamy go
                    result.append(rozkladFormulyORAND(['and', formula[1], formula[2][1]]))
                    result.append(rozkladFormulyORAND(['and', formula[1], formula[2][2]]))
            else:
                # jeśli nie zostawiamy go
                result.append(rozkladFormulyORAND(['and', formula[1], formula[2][1]]))
                result.append(rozkladFormulyORAND(['and', formula[1], formula[2][2]]))

    return upraszczanie(result)


# ------------------------------------------------------#
# Usuwamy duplikaty króre wchodzą do czyszczenia
# [and [or A B] [or B A]] => [or A B]
# ------------------------------------------------------#
def usuwanieDuplikatow(formula):
    # sprawdzamy czy literał jest listą i nie jest negacją
    if len(formula) > 2:
        result = []
        result.append(formula[0])
        result.append(formula[1])

        for i in range(2, len(formula)):
            # dodaj logikę do listy jeśli jest nie jest równa obejcnej
            if not rodzicLogic(result, formula[i]):
                result.append(formula[i])

        # sprawdzmay czy zdanie jest długosci 2
        if len(result) == 2:
            result = result[1]

        return result
    else:
        # zwracam logikę jeśli to jest literał albo negacja
        return formula


# ******************************************************Metody Frazowe*******************************************************#

# ------------------------------------------------------#
# Clean up the logic.
# Merges consecutive similar statements into one
# coherent statement.
# ------------------------------------------------------#
def czyszczenieFrazy(formula):
    # czyszczenie formuły
    formula = czyszczenie(formula)

    # dla wszystkich podformuł też czyścimy
    for i in range(1, len(formula)):
        if len(formula[i]) > 1:
            formula[i] = czyszczenieFrazy(formula[i])

    # Jeszcze raz dla pewności :)
    formula = czyszczenie(formula)

    return formula


# ------------------------------------------------------#
# sprawdza czy w formule znajdują się iff albo imp i zamienia
# je na and i or
# ------------------------------------------------------#
def zamianaIFFiIMP(formula):
    if iffKandydat(formula):
        formula = usuwanieIFF(formula)

    elif impKandydat(formula):
        formula = usuwanieIMP(formula)

    for i in range(1, len(formula)):
        if len(formula[i]) > 1:
            formula[i] = zamianaIFFiIMP(formula[i])

    if iffKandydat(formula):
        formula = usuwanieIFF(formula)

    elif impKandydat(formula):
        formula = usuwanieIMP(formula)
    # zwracanie logiki bez iff i imp
    return formula


# ----------------------------------------------------------#
# Sprawdzamy czy formuła ma negacje nie przy literałach
# stosując prawa De Morgana idziemy rekurencyjnie wgłąb
# ----------------------------------------------------------#
def deMorgan(formula):
    if notKandydat(formula):
        formula = deMorganZamiana(formula)

    for i in range(1, len(formula)):
        if len(formula[i]) > 1:
            formula[i] = deMorgan(formula[i])
    # zwracamy formułe z negacjami tylko przy literałach

    if notKandydat(formula):
        formula = deMorganZamiana(formula)
    return formula


# ----------------------------------------------------------#
# Sprawdzamy czy formuła nadaje się do rozkładu
# na OR przed AND
# ----------------------------------------------------------#
def rozkladFormulyORAND(formula):
    if rozkladKandydat(formula):
        formula = rozkladAND(formula)

    for i in range(1, len(formula)):
        if len(formula[i]) > 1:
            formula[i] = rozkladFormulyORAND(formula[i])

    if rozkladKandydat(formula):
        formula = rozkladAND(formula)
    return upraszczanie(formula)


# ----------------------------------------------------------#
# rukurencyjnie uwuwamy duplikaty w fomule
# przykladowo [A v A] zostaje zamienione na A
# usuwa też logicznie takie same zdania składowe np.
# [A v B] = [B v A]
# ----------------------------------------------------------#
def duplikatyFormuly(formula):
    formula = usuwanieDuplikatow(formula)
    for i in range(1, len(formula)):
        if len(formula[i]) > 1:
            formula[i] = duplikatyFormuly(formula[i])
    formula = usuwanieDuplikatow(formula)
    return formula

def formulaToString(formula):
    finalAPN=""
    if(formula[0]== "or"):
        for i in range(1, len(formula)):
            finalAPN +="("
            if(formula[i][0]== "and"):
                for j in range(1, len(formula[i])):
                    if (len(formula[i][j]) == 1):
                        finalAPN += str(formula[i][j])
                    else:
                        finalAPN += "not " + str(formula[i][j][1])
                    if (formula[i][j] != formula[i][-1]):
                        finalAPN += " and "
                finalAPN += ")"
            elif(formula[i][0] == "not"):
                finalAPN += "not " + str(formula[i][1]) + ")"
            else:
                finalAPN += str(formula[i][0]) + ")"
            if(formula[i]!=formula[-1]):
                finalAPN += " or "
    elif(formula[0] == "and"):
        finalAPN += "("
        for i in range(1, len(formula)):
            if (len(formula[i]) == 1):
                finalAPN += str(formula[i])
            else:
                finalAPN += "not " + str(formula[i][1])
            if (formula[i] != formula[-1]):
                finalAPN += " and "
            else:
                finalAPN+=")"
    return finalAPN

def usuwanieNull(formula):
    for j in range(1, len(formula)):
        if (len(formula[j]) > 1):
            temp = formula[j][1]
            for m in range(1, len(formula)):
                if(temp == formula[m][0]):
                    return True
    return False


def spelnialnoscFormuly(formula):
    popList=[]
    if(formula[0]== "and"):
        if(usuwanieNull(formula)):
            for i in formula:
                formula.remove(i)
            return formula
    for i in range(1, len(formula)):
        if(usuwanieNull(formula[i])):
            popList.append(i)
    for i in reversed(popList):
        del formula[i]
    return formula


# ****************************************************Metody Stosowane*******************************************************#


# ----------------------------------------------------------#
# Przechodzenie formuly do postaci APN
# ----------------------------------------------------------#
def trasnformacja(logic):
    # jeśli formuła jest pusta
    if len(logic) == 0:
        return logic
    # jeśli formuła ma jeden literał
    if len(logic) == 1:
        return logic[0]
    result = zamianaIFFiIMP(logic)
    result = deMorgan(result)
    result = upraszczanie(result)
    result = rozkladFormulyORAND(result)
    result = czyszczenieFrazy(result)
    result = duplikatyFormuly(result)
    result = spelnialnoscFormuly(result)
    result = formulaToString(result)
    if(len(result)>0):
        print("Uproszczona postać APN: ",result)
        print("Formuła jest spełnialna")
        print("")
    else:
        print("Formuła nie jest spełnialna")
        print("")
    return result

# *********************************************************Main**************************************************************#

if __name__ == "__main__":
    trasnformacja(form1)
    trasnformacja(form2)
    trasnformacja(form3)
    trasnformacja(form4)
    trasnformacja(form5)
    trasnformacja(form6)
    trasnformacja(form7)
    trasnformacja(form8)
    trasnformacja(form9)
    trasnformacja(form10)
