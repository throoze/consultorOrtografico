import java.util.Iterator;
import java.util.NoSuchElementException;

//@ model import org.jmlspecs.models.*;

/* Archivo ConsultOrtArreglos.java
 * Autor: Diego Mosquera
 * Creacion: 05/02/10
 * Modificacion: 15/02/10
 */

/**
 * Clase que implementa la interfaz ConsultOrt, la cual modela el tipo abstracto
 * Consultor Ortografico segun lo requerido en el curso de Algoritmos y 
 * Estructuras II de la USB en el periodo Enero-Marzo 2010, primera version 
 * implementada por el Prof. Diego Mosquera, y luego modificada por los alumnos 
 * Victor De Ponte y Jose Zabala.
 * @author Victor De Ponte, carnet 05-38087
 * @author Jose Zabala, carnet 05-39070
 * @version 0.1 23/02/2010
 */
public class ConsultOrtArreglos implements ConsultOrt
{
    // MODELO DE REPRESENTACION CONCRETO:
    
    final static int TAM_INIC = 1;
    private /*@ spec_public @*/ String va[];
    private /*@ spec_public @*/ int tam;
    
    // FIN DEL MODELO DE REPRESENTACION CONCRETO...

    // INVARIANTE DE REPRESENTACION:
    
    /*@ public invariant (\forall int i, j 
      @                         ; 0 <= i && i < this.tam 
      @                             && 
      @                           0 <= j && j < this.tam 
      @                             && 
      @                           i != j
      @                         ; !this.va[i].equals(this.va[j])
      @                  )
      @                  &&
      @                  (\forall int i; 0 <= i && i < this.tam - 1
      @                         ; this.va[i].compareTo(this.va[i + 1]) < 0
      @                  )
      @                  &&
      @                  0 <= this.tam && this.tam <= this.va.length	
      @                  &&
      @                  this.va.length > 0;						 
      @*/
    
    // FIN DEL INVARIANTE DE REPRESENTACION...
    
    // RELACION DE ACOPLAMIENTO:
    
    
    //@ public represents vocabulario <- transformar(this.va, this.tam);
    
                      // FUNCION DE ABSTRACCION:
    
    /*@ public pure model JMLValueSet transformar (String[] c, int t){
      @     JMLValueSet temp = new JMLValueSet();
      @     for (int i = 0; i < t; i++){
      @         temp = temp.union(new JMLValueSet(new JMLString(c[i])));
      @     }
      @     return temp;
      @ }
      @*/

                 // FIN DE LA FUNCION DE ABSTRACCION...
    
    
    // FIN DE LA RELACION DE ACOPLAMIENTO...
    
    // CONSTRUCTOR DEL TIPO:
    
    /**
     * Constructor de la clase, genera un nuevo objeto del tipo 
     * ConsultOrtArreglos.
     */
    /*@ requires true;
      @ ensures this.tam == 0 && this.va.length == this.TAM_INIC;
      @*/
    public ConsultOrtArreglos() {
        this.va = new String[TAM_INIC];
        this.tam = 0;
    }
    
    // FIN DEL CONSTRUCTOR DEL TIPO...
    
    // OPERACIONES DEL TIPO:
    
    /**
     * Operacion encargada de agregar una nueva palabra al vocabulario de this
     * ConsultOrtArreglos. Arroja las excepciones 
     * 'ExcepcionPalabraNoBienFormada' en caso de que !bf(p)
     * y 'ExcepcionPalabraYaRegistrada' en caso de que la palabra ya pertenezca 
     * al vocabulario de este ConsultOrtArreglos.
     * @param p de tipo String La palabra a agregar.
     * @throws ExcepcionPalabraNoBienFormada
     * @throws ExcepcionPalabraYaRegistrada
     */
    /* agregado a los requires del normal behavior: this.bf(p) && !this.pertenece(p)
     * debido a problemas con excepciones...
     */
    /*@ also
      @ normal_behavior
      @ requires this.bf(p) && !this.pertenece(p) && tam < va.length;
      @ ensures tam == \old(tam) + 1 
      @         && 
      @         va[bb(va, p)].equals(p);
      @ ensures (\forall int i; 0 <= i && i < bb(va, p); 
      @                              \old(va[i]).equals(va[i]))		
      @         &&
      @         (\forall int i; bb(va, p) < i && i < \old(tam); 
      @                              \old(va[i-1]).equals(va[i]));
      @ assignable va, tam;
      @
      @ also 
      @ normal_behavior 
      @ requires this.bf(p) && !this.pertenece(p) && tam == va.length;
      @ ensures va.length == 2 * \old(va).length;
      @ ensures (\forall int i; 0 <= i && i < bb(va, p); 
      @                      \old(va[i]).equals(va[i]))		
      @         &&
      @         (\forall int i; bb(va, p) < i && i < \old(tam);
      @                             \old(va[i-1]).equals(va[i]));
      @ ensures tam == \old(tam) + 1 && va[bb(va, p)].equals(p);	
      @ assignable \nothing;
      @	
      @ also 
      @ public exceptional_behavior
      @ requires !bf(p)
      @          ||
      @          this.pertenece(p);
      @ signals_only ExcepcionPalabraNoBienFormada,
      @              ExcepcionPalabraYaRegistrada;
      @ signals (ExcepcionPalabraNoBienFormada) !bf(p);
      @ signals (ExcepcionPalabraYaRegistrada) this.pertenece(p);
      @ assignable \nothing;
      @*/	  
    public void agregar(String p) throws 
            ExcepcionPalabraNoBienFormada,
            ExcepcionPalabraYaRegistrada
    {
        if (!bf(p)) {
            throw new ExcepcionPalabraNoBienFormada("La palabra \""+p+"\" esta mal formada...");
        } else {
            int posi = bb(va, p);
            if (posi < this.tam && va[posi].equals(p)) {
                throw new ExcepcionPalabraYaRegistrada("La palabra \""+p+"\" ya esta registrada...");
            } else {
                if (this.tam == this.va.length){
                    String vtemp[] = new String[2 * va.length];
                    /*@ loop_invariant 0 <= i && i <= va.length &&
                      @             (\forall int k; 0 <= k && k < i;
                      @                 vtemp[k].equals(va[k])
                      @             );
                      @ decreasing va.length - i;
                      @*/ 
                    for (int i = 0; i < va.length; i++){
                        vtemp[i] = va[i];
                    }
                    va = vtemp;
                }
                /*@ loop_invariant posi <= i && i <=this.tam &&
                  @                (\forall int k,l; 0 <= k && k <  i &&
                  @                                  i <  l && l <= this.tam; 
                  @                     this.va[k].equals(\old(this.va[k])) &&
                  @                     this.va[k].equals(\old(this.va[k])) &&
                  @                     this.va[i].equals(\old(this.va[i-1]))
                  @                );
                  @ decreasing i;
                  @*/
                for (int i = this.tam; i > posi; i--){
                    va[i] = va[i-1];
                }
                va[posi] = p;
                tam++;
            }
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
      @             (\forall int i ; 0 <= i && i < p.length()
      @                 ; 0 <= p.charAt(i) - 'a'
      @                 &&
      @                 p.charAt(i) - 'a' <= 25
      @             )
      @         );
      @ assignable \nothing;
      @*/
    public /*@ pure @*/ boolean bf (String p) {
        if (!p.equals("")) {
            boolean bf = true;
            /*@ loop_invariant 0 <= k && k <= p.length() &&
            @         bf <==> (!p.equals("") &&
            @                     (\forall int i; 0 <= i && i < k;
            @                         0 <= p.charAt(i) - 'a'
            @                         &&
            @                         p.charAt(i) - 'a' <= 25 
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
      @             (\forall int i ; 0 <= i && i < p.length() 
      @                 ; p.charAt(i) - q.charAt(i) == 0
      @             );
      @ assignable \nothing;
      @*/
    public /*@ pure @*/ boolean ipf (String p, String q) {
        boolean ipf = true;
        if (p.length() <= q.length()) {
            /*@ loop_invariant 0 <= k && k <= p.length() &&
              @                (\forall int i; 0 <= i && i < k;
              @                         p.charAt(i) - q.charAt(i) == 0
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

    /**
     * Operacion que devuelve un arreglo de Strings que contiene todas las 
     * palabras que estan en el vocabulario de this ConsultOrtArreglos de las
     * cuales la palabra pasada como argumento es prefijo
     * @param pr String, prefijo por el cual se buscara en el vocabulario de 
     *           this ConsultOrtArreglos
     * @return Un arreglo de Strings que contiene todas las palabras que estan 
     *         en el vocabulario de this ConsultOrtArreglos de las cuales la 
     *         palabra pasada como argumento es prefijo. En caso de no conseguir
     *         ninguna palabra para ese prefijo, devuelve un arreglo de tamano
     *         cero (0).
     * @throws ExcepcionPalabraNoBienFormada
     */
    /*@ also
      @ public normal_behavior
      @ requires bf(pr);
      @ ensures (\forall int i;
      @                 0 <= i && i < this.tam;
      @                         this.va[i] == \old(this.va[i])
      @         );
      @ ensures this.tam == \old(this.tam);
      @ ensures (\forall int i, j ;
      @                     0 <= i && i < \result.length
      @                     &&
      @                     0 <= j && j < \result.length
      @                     &&
      @                     i != j;
      @                                 !\result[i].equals(\result[j])
      @         );
      @ ensures (\forall int i ;
      @                 0 <= i && i < \result.length;
      @                         (\exists int j;
      @                                 0 <= j && j < this.tam;
      @                                         this.va[j].equals(\result[i])
      @                         )
      @         );
      @ ensures (\forall int i ;
      @                     0 <= i && i < \result.length;
      @                                 ipf(pr, \result[i])
      @         );
      @ ensures (\forall int i,j;
      @             0 <= i && i < this.tam && 
      @             0 <= j && j < \result.length &&
      @             !this.va[i].equals(\result[j]);
      @             !ipf(pr,this.va[i])
      @         );
      @ assignable \nothing;
      @
      @ also 
      @ public exceptional_behavior
      @ requires !bf(pr);
      @ signals_only ExcepcionPalabraNoBienFormada;
      @ signals (ExcepcionPalabraNoBienFormada) !bf(pr);
      @ assignable \nothing;
      @
      @*/
    public String[] consultarPorPrefijo(String pr) throws
            ExcepcionPalabraNoBienFormada
    {
        if (this.bf(pr)) {
            int start = this.bb(va, pr);
            int end   = start;
            /*@ loop_invariant start <= k && k <= this.tam &&
              @           end == start + (\num_of int i; 0 <= i && i < k;
              @                                 this.ipf(pr, va[i])
              @                          );
              @ decreasing this.tam - k;
              @*/ 
            for (int k = start; k < this.tam && this.ipf(pr, this.va[k]); k++) {
                end++;
            }
            String[] list;
            if (0 < (end - start)) {
                list = new String[end - start];                
                /*@ loop_invariant 0 <= k && k <= list.length &&
                  @                (\forall int i; 0 <= i && i < k;
                  @                            list[i].equals(this.va[start + i])
                  @                );
                  @ decreasing list.length - k;
                  @*/ 
                for (int k = 0; k < list.length; k++) {
                    list[k] = this.va[start + k];
                }
                return list;
            } else {
                list = new String[0];
                return list;
            }
        } else {
            throw new ExcepcionPalabraNoBienFormada("La palabra \""+pr+"\" esta mal formada...");
        }
    }	

    /*@ also
      @ public normal_behavior
      @ requires bf(pl);
      @ ensures this.va.equals(\old(this.va))
      @         &&
      @         (
      @             ( (!(\result.equals(""))) &&
      @                 ipf(\result, pl)
      @                 &&
      @                 (\exists int i;
      @                     0 <= i && i < this.tam;
      @                         (\exists int j;
      @                             0 < j && j <= pl.length();
      @                                 ipf(pl.substring(0, j),this.va[i])
      @                                 &&
      @                                 pl.substring(0, j).equals(\result)
      @                         )
      @                 )
      @             )
      @             ||
      @             (\result.equals("") &&
      @                 (\forall int i;
      @                     0 <= i && i < this.tam;
      @                         !(\exists int j;
      @                              0 < j && j <= pl.length();
      @                                  ipf(pl.substring(0, j),this.va[i])
      @                          )
      @                 )
      @             )
      @         );
      @ assignable \nothing;
      @
      @ also 
      @ public exceptional_behavior
      @ requires !bf(pl);
      @ signals_only ExcepcionPalabraNoBienFormada;
      @ signals (ExcepcionPalabraNoBienFormada) !bf(pl);
      @ assignable \nothing;
      @*/
    public String prefijoMasLargo(String pl) throws 
            ExcepcionPalabraNoBienFormada
    {
        if (this.bf(pl)) {
            String pref = "";
            boolean found = false;
            /*@ loop_invariant 0 <= k && k <= pl.length() &&
              @     ( (!(pref.equals(""))) ? ipf(pref, pl) : true ) &&
              @     (
              @         (\exists int i;
              @             0 <= i && i < this.tam;
              @                 (\exists int j;
              @                     k < j && j <= pl.length();
              @                         ipf(pl.substring(0, j),this.va[i])
              @                 )
              @         )
              @         <==> 
              @         found
              @     );
              @ decreasing k;
              @*/
            for (int k = pl.length(); 0 < k && !found; k--) {
                pref = pl.substring(0, k);
                if (this.haypl(pref)) {
                    found = true;
                } else {
                    found = false;
                }
            }
            return pref;
        } else {
            throw new ExcepcionPalabraNoBienFormada("La palabra \""+pl+"\" esta mal formada...");
        }
    }
    
    
    /*@ also
      @ requires true;
      @ ensures \result != null;
      @*/
    public Iterator elems () {
        return new elGenArr(this.va, this.tam);
    }
    
    // FIN DE LAS OPERACIONES DEL TIPO...
    
    // CLASE INTERNA ESTATICA 'elGen':
    /**
     * Clase estatica privada interna para el tipo ConsultOrtArreglos. Implemen-
     * ta la interface 'Iterator', generando un iterador que recorre todos los 
     * elementos del vocabulario de this ConsultOrtArreglos.
     */
    private static class elGenArr implements Iterator {
        
        private /*@ spec_public @*/ String[] seq;
        private /*@ spec_public @*/ int index;
        
        //@ public represents moreElements <- this.hasNext();
        // set returnsNull = false;
        
        /*@ requires true;
          @ ensures this.seq.length == t;
          @ ensures (\forall int i; 
          @                 0 <= i && i < this.seq.length;
          @                         this.seq[i].equals(s[i])
          @         );
          @ ensures this.index == 0;
          @*/
        public elGenArr (String[] s, int t) {
            this.seq = new String[t];
            for (int k = 0; k < t; k++) {
                this.seq[k] = s[k];
            }
            this.index = 0;
        }
        
        /*@ also
          @ requires true;
          @ ensures \result <==> (this.index < this.seq.length);
          @*/
        public /*@ pure @*/ boolean hasNext () {
            return (this.index < this.seq.length);
        }
        
        /*@ also
          @ public normal_behavior
          @ requires this.hasNext();
          @ ensures this.index == \old(this.index) + 1;
          @ ensures \result == this.seq[\old(this.index)];
          @ assignable this.index;
          @
          @ also
          @ public exceptional_behavior
          @ requires !this.hasNext();
          @ signals_only NoSuchElementException;
          @ signals (NoSuchElementException) !this.hasNext();
          @ assignable \nothing;
          @*/ 
        public Object next () throws NoSuchElementException {
            if (this.hasNext()){
                this.index++;
                return this.seq[this.index - 1];
            } else {
                return new NoSuchElementException("Ya no hay mas elementos...");
            }
        }
        
        /*@ also
          @ requires true;
          @ ensures true;
          @ assignable \nothing;
          @*/ 
        public void remove() {
            System.out.println("Operacion no implementada para este tipo...");
        }
        
    }
    // FIN DE LA CLASE INTERNA ESTATICA 'elGen'...
    
    // OPERACIONES INTERNAS PRIVADAS AUXILIARES:
            
    /**
     * Implementa la busqueda binaria en arreglos de Strings. Mas eficiente que 
     * la busqueda lineal. Requiere que exista una relacion de orden para el 
     * tipo de elementos del arreglo y que el arreglo de entrada este ordenado.
     * @param a el arreglo de Strings a leer.
     * @param s el elemento de tipo String a buscar en 'a'
     * @return posicion en la que se consiguio 's' en caso de estar en 'a'. 
     *         Si 's' no esta en 'a', devuelve la posicion donde deberia estar 
     *         el elemento 's'.
     */
    /*@ requires (this.tam>=0) && 
      @          (\forall int i; 0 <= i && i < this.tam - 1; 
      @                a[i].compareTo(a[i+1]) <= 0
      @          );
      @ 
      @ ensures (0 <= \result && \result <= this.tam); 
      @ ensures (0 <= \result && \result < this.tam && a[\result].equals(s))
      @         ==>
      @         (\exists int i ; 0 <= i && i < this.tam;
      @                 (\forall int j; 0 <= j && j < this.tam && i != j;
      @                         a[i].compareTo(s) == 0 &&
      @                         a[i].compareTo(a[j]) != 0
      @                 )
      @         );
      @ ensures (0 <= \result && \result < this.tam && !a[\result].equals(s))
      @         ==> 
      @         (
      @             (\forall int i ; 0 <= i && i < this.tam;
      @                         a[i].compareTo(s) != 0
      @             )
      @             &&
      @             (\forall int i; 0 <= i && i < \result;
      @                         a[i].compareTo(s) < 0
      @             ) 
      @             &&    
      @             (\forall int j; \result <= j && j < this.tam;
      @                         s.compareTo(a[j]) < 0
      @             )
      @         );
      @ ensures (\forall int i; 0 <= i && i < this.tam; a[i].compareTo(s) < 0) 
      @         ==> 
      @         ( \result == this.tam );
      @ ensures ( (this.tam == 0) ==> (\result == 0) );
      @*/
    private /*@ spec_public pure @*/ int bb (String a[], String s) {
        int     pos=0;
        int     izq=0;
        int     der  = this.tam;
        boolean esta = false;
        /*@ loop_invariant 0 <= izq && izq <= der && der <= this.tam &&
          @                ( esta || (\exists int i; izq <= i && i < der; 
          @                                a[i].equals(s)
          @                          )
          @                          <==>
          @                          (\exists int i; 0 <= i && 
          @                                          i < this.tam;
          @                                a[i].equals(s)
          @                          )
          @                ) &&
          @                (
          @                     (esta ==> (0 <= pos && pos < this.tam &&
          @                                 a[pos].equals(s)
          @                                )
          @                     )
          @                     &&
          @                     ((izq == der && !esta) ==>
          @                         (\forall int i,j; 
          @                             0 <= i && i < pos && pos <= j &&
          @                                 j < this.tam;
          @                                     a[i].compareTo(s) < 0 &&
          @                                     s.compareTo(a[j]) < 0
          @                         )
          @                     )
          @                );
          @ 
          @ decreasing (der-izq)+(!esta ? 1:0);
          @*/
        while (izq!=der && !esta) {
            int med=(izq+der)/2;
            if (a[med].equals(s)) {
                esta=true;
            } else if (a[med].compareTo(s)<0) {
                izq=med+1;
            } else if (a[med].compareTo(s)>0) {
                der=med;
            }
            pos = ( esta ? med : der);
        }
        return pos;
    }
    
    /*@ requires true;
      @ ensures \result <==> (\exists int i; 0 <= i && i < this.tam;
      @                             this.ipf(pf, this.va[i])
      @                      );
      @ assignable \nothing;
      @*/
    private /*@ spec_public pure @*/ boolean haypl (String pf) {
        if (this.bf(pf)) {
            int start = this.bb(va, pf);
            int end   = start;
            /*@ loop_invariant start <= k && k <= this.tam &&
              @           end == start + (\num_of int i; 0 <= i && i < k;
              @                                 this.ipf(pf, va[i])
              @                          );
              @ decreasing this.tam - k;
              @*/ 
            for (int k = start; k < this.tam && this.ipf(pf, this.va[k]); k++) {
                end++;
            }
            return ((0 < (end - start)) ? true : false );
        } else {
            return false;
        }
    }
    
    /**
     * Operacion booleana que devuelve 'true' si el String de entrada pertenece
     * al vocabulario de this ConsultOrtArreglos.
     * @param p String, Palabra a revisar.
     * @return 'true' - si 'p' esta registrada en el vocabulario de this 
     *         ConsultOrtArreglos.
     *         'false' - si 'p' no esta registrada en el vocabulario de this 
     *         ConsultOrtArreglos.
     */
    /*@ public normal_behavior
      @ requires bf(p);
      @ ensures \result <==> (\exists int i; 0 <= i && i < this.tam;
      @                          this.va[i].equals(p)
      @                      );
      @ assignable \nothing;
      @*/ 
    private /*@ spec_public pure @*/ boolean pertenece (String p) {
        if (!bf(p)) {
            return false;
        } else {
            return (   0 <= this.bb(va, p) && 
                       this.bb(va, p) < this.tam &&
                       this.va[this.bb(va, p)].equals(p)
                   );
        }
    }
    
    // FIN DE LAS OPERACIONES INTERNAS PRIVADAS AUXILIARES...
    
// FIN DEL TAD...
}