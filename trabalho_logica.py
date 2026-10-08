# =====================================================================
# TRABALHO DE LÓGICA PARA COMPUTAÇÃO - SAT & A VIAGEM DE CHIHIRO
# =====================================================================

# --- R1: ESTRUTURA DE DADOS (ÁRVORE SINTÁTICA) ---

class Formula:
    def __str__(self):
        raise NotImplementedError
    
    def evaluate(self, valuation):
        raise NotImplementedError
    
    def get_vars(self):
        raise NotImplementedError
    
    def to_nnf(self):
        raise NotImplementedError
    
    def distribute(self):
        return self
    
    def to_cnf(self):
        nnf = self.elim_implies_equiv().to_nnf()
        return nnf.distribute()

    def elim_implies_equiv(self):
        raise NotImplementedError

class Var(Formula):
    def __init__(self, name):
        self.name = name
    
    def __str__(self):
        return self.name
    
    def evaluate(self, valuation):
        return valuation[self.name]
    
    def get_vars(self):
        return {self.name}
    
    def elim_implies_equiv(self):
        return self
    
    def to_nnf(self):
        return self

class Not(Formula):
    def __init__(self, sub):
        self.sub = sub
    
    def __str__(self):
        if isinstance(self.sub, Var):
            return f"¬{self.sub}"
        return f"¬({self.sub})"
    
    def evaluate(self, valuation):
        return not self.sub.evaluate(valuation)
    
    def get_vars(self):
        return self.sub.get_vars()
    
    def elim_implies_equiv(self):
        return Not(self.sub.elim_implies_equiv())
    
    def to_nnf(self):
        sub = self.sub
        if isinstance(sub, Not):
            return sub.sub.to_nnf()
        elif isinstance(sub, And):
            return Or(Not(sub.left).to_nnf(), Not(sub.right).to_nnf())
        elif isinstance(sub, Or):
            return And(Not(sub.left).to_nnf(), Not(sub.right).to_nnf())
        else:
            return Not(sub.to_nnf())

class BinaryOp(Formula):
    def __init__(self, left, right):
        self.left = left
        self.right = right

class And(BinaryOp):
    def __str__(self):
        return f"({self.left} ∧ {self.right})"
    def evaluate(self, valuation):
        return self.left.evaluate(valuation) and self.right.evaluate(valuation)
    def get_vars(self):
        return self.left.get_vars().union(self.right.get_vars())
    def elim_implies_equiv(self):
        return And(self.left.elim_implies_equiv(), self.right.elim_implies_equiv())
    def to_nnf(self):
        return And(self.left.to_nnf(), self.right.to_nnf())
    def distribute(self):
        return And(self.left.distribute(), self.right.distribute())

class Or(BinaryOp):
    def __str__(self):
        return f"({self.left} ∨ {self.right})"
    def evaluate(self, valuation):
        return self.left.evaluate(valuation) or self.right.evaluate(valuation)
    def get_vars(self):
        return self.left.get_vars().union(self.right.get_vars())
    def elim_implies_equiv(self):
        return Or(Not(self.left.elim_implies_equiv()), self.right.elim_implies_equiv())
    def to_nnf(self):
        return Or(self.left.to_nnf(), self.right.to_nnf())
    def distribute(self):
        l = self.left.distribute()
        r = self.right.distribute()
        if isinstance(l, And):
            return And(Or(l.left, r).distribute(), Or(l.right, r).distribute())
        if isinstance(r, And):
            return And(Or(l, r.left).distribute(), Or(l, r.right).distribute())
        return Or(l, r)

class Implies(BinaryOp):
    def __str__(self):
        return f"({self.left} → {self.right})"
    def evaluate(self, valuation):
        return (not self.left.evaluate(valuation)) or self.right.evaluate(valuation)
    def get_vars(self):
        return self.left.get_vars().union(self.right.get_vars())
    def elim_implies_equiv(self):
        return Or(Not(self.left.elim_implies_equiv()), self.right.elim_implies_equiv())
    def to_nnf(self):
        return self

class Equiv(BinaryOp):
    def __str__(self):
        return f"({self.left} ↔ {self.right})"
    def evaluate(self, valuation):
        return self.left.evaluate(valuation) == self.right.evaluate(valuation)
    def get_vars(self):
        return self.left.get_vars().union(self.right.get_vars())
    def elim_implies_equiv(self):
        l = self.left.elim_implies_equiv()
        r = self.right.elim_implies_equiv()
        return And(Or(Not(l), r), Or(Not(r), l))
    def to_nnf(self):
        return self


# --- R3: BUSCA DE MODELOS POR FORÇA BRUTA ---

def generate_valuations(variables):
    vars_list = sorted(list(variables)) # cria a lista de variaveis em ordem alfabetica
    n = len(vars_list) # quantidade de variavesi
    valuations = [] # guarda cada linha da tabela em formato dicionario
    for i in range(1 << n): # ira percorrer a tabela
        val = {} # cria o dicionario ex: {'P': True, 'Q': False}
        for j in range(n): # passa por cada varivael da linha
            val[vars_list[j]] = bool((i >> j) & 1) # transformação do bit em booleano
        valuations.append(val) #terminando a linha joga para a lista
    return valuations # devolve a lista completa

def analyze_formula(formula):
    variables = formula.get_vars()
    valuations = generate_valuations(variables)
    
    models = []
    for val in valuations:
        if formula.evaluate(val):
            models.append(val)
            
    total = len(valuations)
    count = len(models)
    
    if count == 0:
        classification = "Insatisfatível (Contradição)"
    elif count == total:
        classification = "Válida (Tautologia)"
    else:
        classification = "Contingente"
        
    return {
        "satisfativel": count > 0,
        "classificacao": classification,
        "total_avaliacoes": total,
        "total_modelos": count,
        "modelos": models
    }


# --- R4: EXTRAÇÃO DE CLÁUSULAS (FNC) ---

def formula_to_clauses(formula_cnf):
    clauses = [] # cria a lista de clausulas
    
    def extract(node):
        if isinstance(node, And): #percorre a arvore procurndos os ands 2x direito e esquerdo
            extract(node.left)
            extract(node.right)
        else:
            clause = [] # guarda as letras do parentesses
            def extract_literals(n): # vasculhar dntro dos parenteses
                if isinstance(n, Or):
                    extract_literals(n.left) #procura os or esquerda e direita
                    extract_literals(n.right)
                elif isinstance(n, Not):
                    if isinstance(n.sub, Var):
                        clause.append(('~', n.sub.name)) #se esbarrar em um not quadra no parentese com um ~
                elif isinstance(n, Var):
                    clause.append(('', n.name)) # se for variavel guarda com uma tupla vazia e o nome
            extract_literals(node)
            if clause:
                clauses.append(clause) # salva a clausula
                
    extract(formula_cnf)
    return clauses


# --- R5: PROBLEMA-CONTEXTO (A VIAGEM DE CHIHIRO) ---

def rodar_contexto_chihiro():
    print("=" * 60)
    print("R5: APLICAÇÃO AO PROBLEMA-CONTEXTO (A VIAGEM DE CHIHIRO)")
    print("=" * 60)
    
    A = Var('A')
    B = Var('B')
    C = Var('C')
    D = Var('D')
    E = Var('E')
    F = Var('F')
    G = Var('G')
    H = Var('H')
    I = Var('I')

    # Fórmula escolhida: [({(G -> ¬H) ∧ [F ∨ (C -> D)]} -> E) ∧ A ∧ ¬I] -> B
    parte1 = Implies(G, Not(H))
    parte2 = Or(F, Implies(C, D))
    parte3 = And(parte1, parte2)
    parte4 = Implies(parte3, E)
    parte5 = And(And(parte4, A), Not(I))
    formula_chihiro = Implies(parte5, B)

    print(f"\nFórmula Original:\n{formula_chihiro}\n")

    analise = analyze_formula(formula_chihiro)
    print(f"Classificação: {analise['classificacao']}")
    print(f"Total de Modelos Encontrados: {analise['total_modelos']}")

    if analise['modelos']:
        print("\n--- Exemplo de Solução (Modelo de Final Feliz: B = True) ---")
        # Procura um modelo onde o final feliz (B) realmente aconteceu
        modelo_feliz = None
        for m in analise['modelos']:
            if m['B'] == True and m['A'] == True and m['I'] == False:
                modelo_feliz = m
                break
        # Se não achar com todas restrições ativas, pega o primeiro onde B é True
        if not modelo_feliz:
            for m in analise['modelos']:
                if m['B'] == True:
                    modelo_feliz = m
                    break
        if not modelo_feliz:
            modelo_feliz = analise['modelos'][0]
            
        explicar_modelo_chihiro(modelo_feliz)

    print("\n--- Variante Insatisfatível (Tentativa de quebrar a lógica) ---")
    # Tentativa impossível: As premissas de sucesso acontecem (A, E, etc.), mas tentamos forçar B como Falso
    variante_insat = And(formula_chihiro, And(A, And(Not(I), And(E, And(G, And(Not(H), And(F, And(C, And(D, Not(B))))))))))
    analise_insat = analyze_formula(variante_insat)
    print(f"Classificação da Variante: {analise_insat['classificacao']}")
    print(f"Total de Modelos: {analise_insat['total_modelos']} (Comprovadamente Insatisfatível)\n")


def explicar_modelo_chihiro(val):
    traducao = {
        'A': ("Chihiro acertou os pais no chiqueiro", val['A']),
        'B': ("Chihiro foi embora livre com os pais humanos", val['B']),
        'C': ("Yubaba entregou o contrato", val['C']),
        'D': ("Chihiro garantiu seu emprego", val['D']),
        'E': ("Chihiro e sua jornada foram salvas", val['E']),
        'F': ("Chihiro prendeu a respiração na ponte", val['F']),
        'G': ("Chihiro comeu a frutinha mágica", val['G']),
        'H': ("Chihiro desapareceu no mundo espiritual", val['H']),
        'I': ("Chihiro esqueceu seu próprio nome", val['I'])
    }
    for var, (descricao, status) in traducao.items():
        estado = "VERDADEIRO (Aconteceu)" if status else "FALSO (Não aconteceu)"
        print(f"  [{var}] {descricao} -> {estado}")


# --- R6: BATERIA DE TESTES ---

def rodar_testes():
    print("=" * 60)
    print("R6: BATERIA DE TESTES AUTOMÁTICOS")
    print("=" * 60)

    p = Var('P')
    q = Var('Q')

    t1 = Or(p, Not(p))
    res1 = analyze_formula(t1)
    print(f"Teste 1 (Tautologia P ∨ ¬P): {res1['classificacao']} (Esperado: Válida)")
    assert res1['classificacao'].startswith("Válida")

    t2 = And(p, Not(p))
    res2 = analyze_formula(t2)
    print(f"Teste 2 (Contradição P ∧ ¬P): {res2['classificacao']} (Esperado: Insatisfatível)")
    assert res2['classificacao'].startswith("Insatisfatível")

    t3 = Implies(p, q)
    res3 = analyze_formula(t3)
    print(f"Teste 3 (Contingência P → Q): {res3['classificacao']} (Esperado: Contingente)")
    assert res3['classificacao'] == "Contingente"

    print("\nTeste 4 (Verificação de Equivalência FNC via Tabela-Verdade):")
    formula_teste = Implies(p, q)
    cnf_teste = formula_teste.to_cnf()
    
    vars_f = formula_teste.get_vars()
    vals = generate_valuations(vars_f)
    
    equivalentes = True
    for v in vals:
        if formula_teste.evaluate(v) != cnf_teste.evaluate(v):
            equivalentes = False
            break
            
    print(f"Fórmula Original: {formula_teste}")
    print(f"Fórmula FNC Gerada: {cnf_teste}")
    print(f"Cláusulas FNC: {formula_to_clauses(cnf_teste)}")
    print(f"Tabelas-verdade idênticas para todos os casos? {equivalentes} (Esperado: True)")
    assert equivalentes
    print("\nTodos os testes passaram com sucesso!\n")


if __name__ == "__main__":
    rodar_testes()
    rodar_contexto_chihiro()