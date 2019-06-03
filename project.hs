import Data.List
import Data.Char

data Tree = Val Float | Var String | Op Tree String Tree | Fu String Tree --deriving Show

instance Show Tree where
   show (Val x) = show x 
   show (Var x) = x
   show (Fu e r) = if precendence r >=2 || precendence r <= 5 then e ++ " " ++ "( " ++ (show r) ++ " )" else e ++ " " ++ (show r)
   show (Op l e r) = left ++ " " ++ e ++ " " ++ right
      where left = if leftNeedParen then "( " ++ (show l) ++ " )" else show l
            right = if rightNeedParen then "( " ++ (show r) ++ " )" else show r
            leftNeedParen = (precendence l < precendence (Op l e r)) || ((precendence l == precendence (Op l e r)) && (rightAssoc (Op l e r)))
            rightNeedParen = (precendence r < precendence (Op l e r)) || ((precendence r == precendence (Op l e r)) && (leftAssoc (Op l e r)))

precendence :: Tree -> Int
precendence (Var _) = 6 
precendence (Val _) = 6
precendence (Fu _ _) = 5
precendence (Op _ e _)
   | e == "^" = 4
   | e `elem` ["*","/"] = 3
   | e `elem` ["+","-"] = 2
   | otherwise = 0

leftAssoc :: Tree -> Bool
leftAssoc (Var _) = False 
leftAssoc (Val _) = False
leftAssoc (Op _ e _) = e `notElem` ["^","*","+"]

rightAssoc :: Tree -> Bool
rightAssoc (Var _) = False 
rightAssoc (Val _) = False
rightAssoc (Op _ e _) = e == "^"

isFunction e = e `elem` ["sin","cos","exp","log"]
isOperator e = e `elem` ["+","-","*","/","^"]

buildExp x = buildExp' x []
   where buildExp' [] a = a
         buildExp' (x:xs) a
            | isOperator x == False && isFunction x == False && (head x) `elem` "0123456789" = buildExp' xs (Val (toFloat x) : a) --
            | isOperator x == False && isFunction x == False && (head x) `elem` ['a'..'z'] = buildExp' xs (Var x : a) --
            | isOperator x = buildExp' xs ((Op (head (tail a)) x (head a)) : (tail (tail a)))
            | otherwise = buildExp' xs ((Fu x (head a)) : (tail a))

toFloat x = read x :: Float

eval (Val x) = x 
eval (Var x) = error "Tree still contains variables, substitute them before evaluation" --
eval (Op l e r)
   | e == "+" = eval l + eval r
   | e == "-" = eval l - eval r
   | e == "*" = eval l * eval r
   | e == "/" = eval l / eval r
   | e == "^" = eval l ** eval r
   | otherwise = error "didn't find operator"
eval (Fu e r)
   | e == "sin" = sin (eval r)
   | e == "cos" = cos (eval r)
   | e == "log" = log (eval r)
   | e == "exp" = exp (eval r)
   | otherwise = error "didn't find function"

--s - variable, e - expression, v - value
substitute s e v = [substitute' s (head e) v]
substitute' s (Val x) v = (Val x)
substitute' s (Var x) v = if x == s then (Val (toFloat v)) else (Var x) 
substitute' s (Op l e r) v = (Op (substitute' s l v) e (substitute' s r v))
substitute' s (Fu e r) v = (Fu e (substitute' s r v))

--HasVariable e s = HasVariable' e s
hasVariable (Val x) s = False
hasVariable (Var x) s = x == s
hasVariable (Op l e r) s = (hasVariable l s) || (hasVariable r s)
hasVariable (Fu e r) s = hasVariable r s

isVa (Val x) = True
isVa _ = False

isVar (Var x) s = if x == s then True else False
isVar _ s = False

derivePM (Op l e r) s
   | isVa l && isVa r = (Val 0)
   | isVa l && not (isVa r) = (Op (Val 0) e (derive' r s))
   | isVa r && not (isVa l) = (Op (derive' l s) e (Val 0))
   | isVar l s && not (isVar r s) = (Op (Val 1) e (derive' r s))
   | isVar r s && not (isVar l s) = (Op (derive' l s) e (Val 1))
   | isVar l s && isVar r s = (Op (Val 1) e (Val 1))
   | otherwise = (Op (derive' l s) e (derive' r s))

deriveMD (Op l e r) s
   | hasVariable (Op l e r) s = (Op (derive' l s) e (derive' r s))
   | otherwise = (Val 0)

derive e s = [derive' (head e) s]
derive' (Var x) s = if isVar (Var x) s then (Val 1) else (Val 0)
derive' (Val x) s = (Val x)

derive' (Op l e r) s
   | e `elem` ["+","-"] = derivePM (Op l e r) s
   | e `elem` ["*","/"] = deriveMD (Op l e r) s
   | e == "^" && hasVariable l s = (Op r "*" (Op l "^" (Op r "-" (Val 1))))
   | otherwise = (Val 0)
derive' (Fu e r) s
   | e == "sin" && hasVariable r s = (Op (Fu "cos" r) "*" (derive' r s))
   | e == "cos" && hasVariable r s = (Op (Op (Val 0) "-" (Fu "sin" r)) "*" (derive' r s))
   | e == "log" && hasVariable r s = (Op (Val 1) "/" r)
   | e == "exp" && hasVariable r s = (Fu "exp" r)
   | otherwise = (Val 0)

optimalize x = [clean (head [clean (head ([clean (head x)]))])]
clean (Val x) = (Val x)
clean (Var x) = (Var x)
clean (Op (Val x) e (Val y)) = (Val (eval (Op (Val x) e (Val y))))
clean (Op l e (Val 0))
   | e `elem` ["+","-"] = l
   | e == "^" = (Val 1)
   | e == "/" = error "divide by 0"
   | otherwise = (Val 0)
clean (Op (Val 0) e r)
   | e `elem` ["+"] = r
   | e == "-" = (Op (Val 0) e r)
   | otherwise = (Val 0)
clean (Op (Val 1) e r)
   | e `elem` ["*"] = r
   | e == "^" = (Val 1)
   | otherwise = (Op (Val 1) e r)
clean (Op l e (Val 1))
   | e `elem` ["*","/","^"] = l
   | otherwise = (Op l e (Val 1))
clean (Op l e r) = (Op (clean l) e (clean r))
clean (Fu e r) = (Fu e (clean r))

order "sin" = 5
order "cos" = 5
order "exp" = 5
order "log" = 5
order "^" = 4
order "*" = 3
order "/" = 3
order "+" = 2
order "-" = 2
order _ = 0

checkOrder o (s:ss) (e:es)
   | s == "(" = shuntingYard o (e:s:ss) es
   | order s >= order e = shuntingYard (s:o) (e:ss) es
   | otherwise = shuntingYard o (e:s:ss) es

--o = output , s = operator stack, e = expression
shuntingYard o s [] = (reverse o) ++ s
shuntingYard o [] (e:es)
   | isFunction e || isOperator e || e == "(" = shuntingYard o [e] es
   | e == ")" = error "mismatched parenthesis"
   | otherwise = shuntingYard (e:o) [] es
shuntingYard o (s:ss) (e:es)
   | e == "(" = shuntingYard o (e:s:ss) es
   | e == ")" = (shuntingYard ((takeWhile (/= "(") (s:ss)) ++ o) (tail (dropWhile (/="(") (s:ss))) es)
   | isFunction e || isOperator e = checkOrder o (s:ss) (e:es)
   | e == "^" = shuntingYard o (e:s:ss) es
   | otherwise = shuntingYard (e:o) (s:ss) es

toPostfix :: String -> String
toPostfix = intercalate " " . shuntingYard [] [] . words

createExpression x = buildExp (words (toPostfix x))

evaluate x = eval $ head x

evaluate' x = eval $ head $ createExpression x