/**
 * Pequena clase con metodos auxiliares que seran utiles a lo largo del desarro-
 * llo de las actividades del curso "Algoritmos y Estructuras II" de la Univer-
 * sidad Simon Bolivar
 * @version 0.1 23 de Enero de 2010
 * @author Victor De Ponte, 05-38087
 */
public class Auxs{
    /*@ requires a.length>0 && 0<=x && x<a.length && 0<=y && y<a.length;
      @ ensures \old(a.length)==a.length && 
      @      (\forall int i ; 0<=i&&i<a.length&&i!=x&&i!=y; \old(a[i])==a[i]) && 
      @      \old(a[x])==a[y] && \old(a[y])==a[x];
      @*/
    public static void intercambiar (int[] a, int x, int y) {
        int aux=a[x];
        a[x]=a[y];
        a[y]=aux;
    }
    
    public static int[] construirArregloAleatorio(int tamano) {
        int[] a=new int[tamano];
        for (int k=0 ; k<a.length ; k++){
            double d = Math.random();
            int e = (new Double(d*(tamano)/2)).intValue();
            int signo = (new Double(d*2)).intValue();
            if (signo==0)
                e=-1*e;
            a[k]=e;
        }
        return a;
    }
    
    /**
     * Funcion que consigue el minimo entre dos enteros
     * @param a entero a comparar
     * @param b entero a comparar
     * @return el minimo entre 'a' y 'b'.
     */
    /*@ requires true;
      @ ensures (\result==a <==> a<=b) && (\result==b <==> b<=a);
      @*/
    public static int minInt(int a,int b) {
        if (a<b)
            return a;
        else
            return b;
    }
    
    /**
     * Funcion que consigue el minimo entre tres enteros
     * @param a entero a comparar
     * @param b entero a comparar
     * @param c entero a comparar
     * @return el minimo entre 'a', 'b' y 'c'.
     */
    /*@ requires true;
      @ ensures (\result==a <==> a<=b && a<=c) && (\result==b <==> b<=a && b<=c)
      @         && (\result==c <==> c<=a && c<=b);
      @*/
    public static int minInt (int a, int b, int c) {
        if (a<=b && a<=c)
            return a;
        else if (b<=a && b<=c)
            return b;
        else
            return c;
    }
    
    /**
     * Funcion que consigue el maximo entre dos enteros
     * @param a entero a comparar
     * @param b entero a comparar
     * @return el minimo entre 'a' y 'b'.
     */
    /*@ requires true;
      @ ensures (\result==a <==> a<=b) && (\result==b <==> b<=a);
      @*/
    public static int maxInt (int a, int b) {
        if (a>b)
            return a;
        else
            return b;
    }
    
    /**
     * Funcion que consigue el maximo entre tres enteros
     * @param a entero a comparar
     * @param b entero a comparar
     * @param c entero a comparar
     * @return el maximo entre 'a', 'b' y 'c'.
     */
    /*@ requires true;
      @ ensures (\result==a <==> a>=b && a>=c) && (\result==b <==> b>=a && b>=c)
      @         && (\result==c <==> c>=a && c>=b);
      @*/
    public static int maxInt (int a, int b, int c) {
        if (a>=b && a>=c)
            return a;
        else if (b>=a && b>=c)
            return b;
        else
            return c;
    }
    
    /*@ requires a.length>0;
      @ ensures true;
      @*/
    public static void print (int[] a) {
        System.out.println("                      ");
        System.out.println("Este es el arreglo:   ");
	System.out.println("                      ");
        System.out.print("{  ");
	/*@ loop_invariant true;
	  @ decreasing a.length-k;
	  @*/
	for (int k=0 ; k<a.length ; k++) {
            System.out.print(a[k]+"  ");
	}
        System.out.println("}");
        System.out.println("                      ");
    }


    public static void printo (int[] a) {
        System.out.println("                      ");
	System.out.println("Este es el arreglo ordenado: ");
	System.out.println("                      ");
        System.out.print("{  ");
	/*@ loop_invariant true;
	  @ decreasing a.length-k;
	  @*/
	for (int k=0 ; k<a.length ; k++){
            System.out.print(a[k]+"  ");
	}
        System.out.println("}");
        System.out.println("                      ");
    }

    /*@ requires a.length>0;
      @ ensures true;
      @*/
    public static void llenarA(int[] a) {
        int s = Console.readInt("Si Desea introducir usted mismo los elementos del arreglo, ingrese uno(1). Si desea que sean generados aleatoriamente, ingrese cero(0): ");
        System.out.println("                      ");
        System.out.println("                      ");
        boolean read=false;
	/*@ loop_invariant true;
	  @ 
	  @*/
	while (!read) {
            if (s==1){
                for (int k=0 ; k<a.length ; k++){
                    System.out.println("                      ");
                    a[k]=Console.readInt("Por favor, introduzca el elemento a["+k+"]: ");
                    System.out.println("                      ");
                }
                read=true;
            } else if (s==0) {
                for (int k=0 ; k<a.length ; k++){
                    double d = Math.random();
		    int e = (new Double(d*(a.length/2))).intValue();
		    int signo = (new Double(d*2)).intValue();
		    if (signo==0)
                        e=-1*e;
		    a[k]=e;
		}
		read=true;
            } else {
                System.out.println("                      ");
                s = Console.readInt("Por favor, ingrese solo un uno(1) o un cero(0). Si Desea introducir usted mismo los elementos del arreglo, ingrese uno(1). Si desea que sean generados aleatoriamente, ingrese cero(0): ");
                System.out.println("                      ");
            }
	}
    }

    public static void main (String[] args)
    {
    
    }
}