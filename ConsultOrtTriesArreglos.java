import java.util.Iterator;
//@ model import org.jmlspecs.models.*;
public class ConsultOrtTriesArreglos implements ConsultOrt {
    
    // MODELO DE REPRESENTACION:
    
    final static int TAMINIC = 26;
    private /*@ spec_public @*/ Nodo vt;
    
    // FIN DEL MODELO DE REPRESENTACION...
    
    // CLASE INTERNA PRIVADA:
    private static class Nodo{
	
        //MODELO DE REPRESENTACION DE LA CLASE INTERNA (Nodo):
        
        public Nodo at[];
        public boolean esPalabra;
        
        // FIN DEL MODELO DE REPRESENTACION DE LA CLASE INTERNA (Nodo)...
        
        // CONSTRUCTOR DE LA CLASE INTERNA (Nodo):
	Nodo(){
            this.at = new Nodo[TAMINIC];
            this.esPalabra = true;
        }
        // FIN DEL CONSTRUCTOR DE LA CLASE INTERNA (Nodo)...
        
        // OPERACIONES DE LA CLASE INTERNA (Nodo):
        /**
     * Operacion que devuelve un valor booleano que indica si el String que se 
     * le pasa es una palabra "bien formada", esto es, cada uno de los 
     * caracteres que lo conforman pertenece al conjunto { a - z } (alfabeto 
     * ingles).
     * @param p
     * @return valor booleano que indica si el String que se le pasa es una 
     *         palabra "bien formada", esto es, cada uno de los caracteres que 
     *         lo conforman pertenece al conjunto { a - z } (alfabeto ingles).
     */
        /*@ requires true;
          @ ensures \result <==> (!p.equals("")
          @             && 
          @             (\forall int e ; 0 <= e && e < p.length() 
          @                 ; 0 <= p.charAt(e) - 'a' 
          @                 &&
          @                 p.charAt(e) - 'a' <= 25
          @             )
          @         );
          @ assignable \nothing;
          @*/
        public /*@ pure @*/ boolean bf (String p) {
            if (!p.equals("")) {
                boolean bf = true;
                /*@ loop_invariant 0 <= k && k <= p.length() &&
                  @         bf <==> (!p.equals("") &&
                  @                     (\forall int e; 0 <= e && e < k;
                  @                         0 <= p.charAt(e) - 'a'
                  @                         &&
                  @                         p.charAt(e) - 'a' <= 25 
                  @                     )
                  @                 );
                  @ decreasing p.length() - k;
                  @*/
                for (int k = 0; k < p.length() && bf; k++) {
                    int code = p.charAt(k) - 'a';
                    bf = (0 <= code && code <= 25);
                }
                return bf;
            
            } else {
                return false;
            }
        }
        
        /*@ requires true;
          @ ensures (this == null && \result <==> true)
          @         ||
          @         (
          @             (this != null)
          @             &&
          @             (   
          @                 \result
          @                 <==>
          @                 (
          @                     (\forall int e;
          @                             0 <= e && e < this.at.length;
          @                                                 this.at[e] == null
          @                     )
          @                     &&
          @                     this.esPalabra
          @                 )
          @             )
          @         );
          @ assignable \nothing;
          @*/
        public /*@ pure @*/ boolean isEmpty() {
            if (this != null) {
                boolean nulo = true;
                /*@ loop_invariant  (0 <= k && k <= this.at.length)
                  @                 &&
                  @                 (
                  @                     nulo 
                  @                     <==>
                  @                     (\forall int e;
                  @                             0 <= e && e < k; 
                  @                                     this.at[e] == null
                  @                     )
                  @                 );
                  @
                  @ decreasing (this.at.length - k);
                  @*/
                for (int k = 0; k < this.at.length && nulo; k++) {
                    if (this.at[k] != null) {
                        nulo = false;
                    }
                }
                if (nulo) {
                    nulo = (this.esPalabra);
                }
                return nulo;
            } else {
                return true;
            }
        }
        
        /*@ requires true;
          @ ensures (!this.bf(p) && \result <==> false)
          @         ||
          @         (
          @             this.bf(p)
          @             &&
          @             \result 
          @             <==>
          @             (
          @                 !this.at[toInt(p,0)].isEmpty()
          @                 && 
          @                 (
          @                     (
          @                         (1 < p.length())
          @                         &&
          @                         this.at[toInt(p,0)].isIn(p.substring(1))
          @                     )
          @                     ||
          @                     (
          @                         (p.length() <= 1)
          @                         &&
          @                         this.esPalabra
          @                     )
          @                 )
          @             )
          @         );
          @ assignable \nothing;
          @ measured_by p.length();
          @*/ 
        public /*@ pure @*/ boolean isIn (String p) {
            if (!this.at[toInt(p,0)].isEmpty()) {
                if (1 < p.length()) {
                    return this.at[toInt(p,0)].isIn(p.substring(1));
                } else {
                    return this.esPalabra;
                }
            } else {
                return false;
            }
        }
        
        
        /*@ requires true;
          @ ensures (this.isEmpty() && \result == 0)
          @         ||
          @         (!this.isEmpty()
          @         &&
          @         \result 
          @         ==
          @         (this.esPalabra ? 1 : 0) + (\sum int i;
          @                                         0 <= i && i < 26;
          @                                             this.at[i].countWords()
          @                                     )
          @         );
          @ assignable \nothing;
          @*/
        public /*@ pure @*/ int countWords () {
            int n = 0;
            if (!this.isEmpty()) {
                /*@ loop_invariant 0 <= k && k <= 26 &&
                  @    n == (\sum int i;
                  @                 0 <= i && i < k;
                  @                         this.at[i].countWords()
                  @         );
                  @ decreasing 26 - k;
                  @*/
                for (int k = 0; k < 26; k++) {
                    n = n + this.at[k].countWords();
                }
                return (n + (this.esPalabra ? 1 : 0));
            } else {
                return 0;
            }
        }
        
        public /*@ pure @*/ String[] extractWordsA () {
            String[] words = new String[0];
            if (!this.isEmpty()) {
                for (int k = 0; k < 26; k++) {
                    if (!this.at[k].isEmpty()) {
                        String[] tmp = this.at[k].extractWordsA();
                        words = new String[(this.esPalabra ? tmp.length + 1 : tmp.length)];
                        if (this.esPalabra) {
                            words[0] = "";
                        }
                        for (int l = (this.esPalabra ? 1 : 0); l < words.length; l++) {
                            words[l] = Character.toString(toChar(k)) + tmp[l];
                        }
                    }
                }
            }
            return words;
        }
        
        
        
        /*@ requires 0 <= tam && tam < a.length;
          @ ensures (\forall int i;
          @                 0 <= i && i < a.length && i != tam;
          @                         a[i].equals(\old(a[i]))
          @         );
          @ ensures a[tam].equals(p);
          @ also
          @ requires tam == a.length;
          @ ensures a.length == 2 * \old(a.length);
          @ ensures (\forall int i;
          @                 0 <= i && i < tam && i != tam;
          @                         a[i].equals(\old(a[i]))
          @         );
          @ ensures a[tam].equals(p);
          @*/
        public static void add (String[] a, String p, int tam) {
            if (tam == a.length) {
                String temp[] = new String[2 * a.length];
                /*@ loop_invariant 0 <= i && i <= a.length &&
                  @             (\forall int k; 0 <= k && k < i;
                  @                 temp[k].equals(a[k])
                  @             );
                  @ decreasing a.length - i;
                  @*/ 
                for (int i = 0; i < a.length; i++){
                    temp[i] = a[i];
                }
                a = temp;
            }
            a[tam] = p;
        }
        
        /*@ requires 0 <= i && i < 26;
          @ ensures 10 <= Character.getNumericValue(\result);
          @ ensures Character.getNumericValue(\result) <= 35;
          @ ensures 0 <= \result - 'a' && \result - 'a' <= 25;
          @ ensures \result - 'a' == i;
          @ assignable \nothing;
          @*/
        public static /*@ pure @*/ char toChar(int i){
            if (i == 0) {return 'a';} else if (i == 1) {return 'b';
            } else if (i == 2) {return 'c';} else if (i == 3) {return 'd';
            } else if (i == 4) {return 'e';} else if (i == 5) {return 'f';
            } else if (i == 6) {return 'g';} else if (i == 7) {return 'h';
            } else if (i == 8) {return 'i';} else if (i == 9) {return 'j';
            } else if (i == 10) {return 'k';} else if (i == 11) {return 'l';
            } else if (i == 12) {return 'm';} else if (i == 13) {return 'n';
            } else if (i == 14) {return 'o';} else if (i == 15) {return 'p';
            } else if (i == 16) {return 'q';} else if (i == 17) {return 'r';
            } else if (i == 18) {return 's';} else if (i == 19) {return 't';
            } else if (i == 20) {return 'u';} else if (i == 21) {return 'v';
            } else if (i == 22) {return 'w';} else if (i == 23) {return 'x';
            } else if (i == 24) {return 'y';} else if (i == 25) {return 'z';
            } else {return 'X';}
        }
        
        /*@ requires !p.equals("");
          @ requires (\forall int e ;
          @                     0 <= e && e < p.length();
          @                                 0 <= p.charAt(e) - 'a' 
          @                                 &&
          @                                 p.charAt(e) - 'a' < 26
          @          );
          @ requires 0 <= n && n < p.length();
          @ ensures \result == (p.charAt(n) - 'a');
          @ ensures 0 <= \result && \result < 26;
          @ assignable \nothing;
          @*/
        public static /*@ pure @*/ int toInt (String p, int n) {
            return (p.charAt(n) - 'a');
        }
        
        public void proc (String s, String pr, int i){
            if (esPalabra) {
                i = i++;
            }
            String l = pr;
            for (int k =0; k < 26; k++){
                if (this.at[k] != null) {
                    l = l + (char)(i + 'a');
                    this.at[k].proc(s,l,i);
                }
            }
            if (this.esPalabra) {
                s = s + l + " ";
            }
        }
        // FIN DE LAS OPERACIONES DE LA CLASE INTERNA (Nodo)...
    }
    // FIN DE LA CLASE INTERNA PRIVADA...
    
    // INVARIANTE DE REPRESENTACION:
    
    //@ public invariant ok(vt);
    
               // FUNCION AUXILIAR DE ABSTRACCION PARA EL INVARIANTE:
    
    /*@ requires t.isEmpty();
      @ ensures \result <==> true;
      @ also 
      @ requires !t.isEmpty();
      @ ensures \result 
      @         <==>
      @         (
      @             (\forall int e; 
      @                     0 <= e && e < 26;
      @                             (t.at[e].isEmpty())==>t.esPalabra
      @             )
      @             && 
      @             (\forall int e;
      @                     0 <= e && e < 26; 
      @                             ok(t.at[e]) 
      @             )
      @         );
      @ public pure model boolean ok(Nodo t){
      @     if (!t.isEmpty()) {
      @         boolean flag = true;
      @         for (int k = 0 ; k < 26 && flag; k++) {
      @             if (!((t.at[k].isEmpty() ==> t.esPalabra) && ok(t.at[k]))) {
      @                 flag = false;
      @             }
      @         }
      @         return flag;
      @     } else {
      @         return true;
      @     }
      @ }
      @*/
    
           // FIN DE LA FUNCION AUXILIAR DE ABSTRACCION PARA EL INVARIANTE...
    
    // FIN DEL INVARIANTE DE REPRESENTACION...
    
    // RELACION DE ACOPLAMIENTO:
    
    /*@ public represents 
            vocabulario <- extr(this.vt).difference(new JMLValueSet(new JMLString("")));
      @*/
                // FUNCION DE ABSTRACCION:
    
    /* requires t.isEmpty();
     * ensures \result.isEmpty();
     * also
     * requires !t.isEmpty();
     * ensures \result == 
     *          {e, x : 0 <= e < 26 && x E extr(a [e]) : toChar(e) o x } U B
     */
    /*@ public pure model JMLValueSet extr(Nodo t) {
      @     JMLValueSet tmp = new JMLValueSet();
      @     for (int k = 0; k < 26; k++) {
      @         if (!t.at[k].isEmpty()) {
      @             Iterator I = extr(t.at[k]).iterator();
      @             while (I.hasNext()) {
      @                 JMLString e = (new JMLString("toChar(k)")) + (new JMLString(I.next()));
      @                 tmp.fast_insert(e);
      @             }
      @         }
      @     }
      @     return tmp;
      @ }
      @*/
                // FIN DE LA RELACION DE ABSTRACCION...
    
    // FIN DE LA RELACION DE ACOPLAMIENTO...
    
    // CONSTRUCTOR DE LA CLASE:
    
    /*@ requires 
      @     true;
      @ ensures 
      @     vt != null;
      @*/		
    public ConsultOrtTriesArreglos()
    {
        vt = new Nodo();
    }
    
    // FIN DEL CONSTRUCTOR DE LA CLASE...
    
    // OPERACIONES DEL TIPO:
    
    /*@ also 
      @ public normal_behavior
      @ assignable vt;
      @*/   
    public void agregar(String p) throws
	    ExcepcionPalabraNoBienFormada, 
	    ExcepcionPalabraYaRegistrada
    {
        if (!bf(p)) {
            throw new ExcepcionPalabraNoBienFormada
                    ("La palabra \""+p+"\" esta mal formada...");
        } else {
            Nodo t = vt;
	    for(int k = 0; k < p.length(); k++){
	        int i = p.charAt(k) - 'a';
	        if (t.at[i] == null) {
	            t.at[i] = new Nodo();
                } else {
		    if (k == p.length() - 1 && t.esPalabra) {
		        throw new ExcepcionPalabraYaRegistrada
                                 ("La palabra \""+p+"\" ya esta registrada...");
                    }
                }
	        t = t.at[i];
	    }
	    t.esPalabra = true;
        }
    }
	
    /**
     * Operacion que devuelve un valor booleano que indica si el String que se 
     * le pasa es una palabra "bien formada", esto es, cada uno de los 
     * caracteres que lo conforman pertenece al conjunto { a - z } (alfabeto 
     * ingles).
     * @param p
     * @return valor booleano que indica si el String que se le pasa es una 
     *         palabra "bien formada", esto es, cada uno de los caracteres que 
     *         lo conforman pertenece al conjunto { a - z } (alfabeto ingles).
     */
    /*@ also
      @ requires true;
      @ ensures \result <==> (!p.equals("")
      @             && 
      @             (\forall int e ; 0 <= e && e < p.length() 
      @                 ; 0 <= p.charAt(e) - 'a' 
      @                 &&
      @                 p.charAt(e) - 'a' <= 25
      @             )
      @         );
      @ assignable \nothing;
      @*/
    public /*@ pure @*/ boolean bf (String p) {
        if (!p.equals("")) {
            boolean bf = true;
            /*@ loop_invariant 0 <= k && k <= p.length() &&
              @         bf <==> (!p.equals("") &&
              @                     (\forall int e; 0 <= e && e < k;
              @                         0 <= p.charAt(e) - 'a'
              @                         &&
              @                         p.charAt(e) - 'a' <= 25 
              @                     )
              @                 );
              @ decreasing p.length() - k;
              @*/
            for (int k = 0; k < p.length() && bf; k++) {
                int code = p.charAt(k) - 'a';
                bf = (0 <= code && code <= 25);
            }
            return bf;

        } else {
            return false;
        }
    }
	
    /**
     * Operacion que devuelve un valor booleano que indica si el primer 
     * parametro pasado es prefijo del segundo parametro pasado (ambos de tipo 
     * String). 
     * @param p de tipo String, prefijo a consultar
     * @param q de tipo String, palabra sobre la cual se consultara el prefijo
     * @return Valos booleano que devuelve 'true' si 'p' es prefijo de 'q' y 
     *         devuelve 'false' en caso contrario.
     */    
    /*@ also
      @ requires bf(p) && bf(q);
      @ ensures \result <==> p.length() <= q.length()
      @             &&
      @             (\forall int e ; 0 <= e && e < p.length() 
      @                 ; p.charAt(e) - q.charAt(e) == 0
      @             );
      @ assignable \nothing;
      @*/
    public /*@ pure @*/ boolean ipf (String p, String q) {
        boolean ipf = true;
        if (p.length() <= q.length()) {
            /*@ loop_invariant 0 <= k && k <= p.length() &&
              @                (\forall int e; 0 <= e && e < k;
              @                         p.charAt(e) - q.charAt(e) == 0
              @                ) <==> ipf;
              @ decreasing p.length() - k;
              @*/
            for (int k = 0; k < p.length() && ipf ; k++) {
                if (!(p.charAt(k) - q.charAt(k) == 0)) {
                    ipf = false;
                }
            }
            return ipf;
        } else {
            return false;
        }
    }

    /*@ also
      @ requires 
            true;
      @ ensures 
            true;
      @*/
    public String[] consultarPorPrefijo(String pr) throws 
        ExcepcionPalabraNoBienFormada
    {
        if (this.bf(pr)) {
            Nodo t = this.vt;
            String[] palabras = new String[0];
            for (int k = 0; k < pr.length(); k++) {
                int e = pr.charAt(k) - 'a';
                if (t.at[e].isEmpty()) {
	            return palabras;
                }
	        t = t.at[e];
            }
            int tam = 0;
            String s = "";
            t.proc(s, pr, tam);
            String[] tmp = t.extractWordsA();
            palabras = new String[(t.esPalabra ? tmp.length + 1 : tmp.length)];
            if (t.esPalabra) {
                palabras[0] = "";
            }
            for (int k = (t.esPalabra ? 1 : 0); k < palabras.length; k++) {
                palabras[k] = pr + tmp[k];
            }
            return palabras;
        } else {
            throw new ExcepcionPalabraNoBienFormada("La palabra \""+pr+"\" esta mal formada...");
        }
    }	

    /*@ also
      @ requires 
            true;
      @ ensures 
            true;
      @*/
    public String prefijoMasLargo(String pl) throws 
        ExcepcionPalabraNoBienFormada
    {
        // COMPLETAR
	return "";
    }

    public Iterator elems() {
        throw new UnsupportedOperationException("Not supported yet.");
    }
    
    // FIN DE LAS OPERACIONES DEL TIPO...
    
    // METODOS AUXILIARES:

    /*@ requires true;
      @ ensures \result <==> this.vt.isEmpty();
      @*/
    private /*@ pure @*/ boolean esTvac () {
        return this.vt.isEmpty();
    }
    
    /*@ requires true;
      @ ensures \result <==> this.vt.isIn(p);
      @*/
    private /*@ pure @*/ boolean pertenece (String p) {
        return this.vt.isIn(p);
    }
    
    /*@ requires true;
      @ ensures \result == this.vt.countWords();
      @*/
    private /*@ pure @*/ int contarPalabras () {
        return this.vt.countWords();
    }
    
    
    
    // FIN DE LOS METODOS AUXILIARES...

// FIN DE LA CLASE...
}